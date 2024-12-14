//! This module implements `TermPool`, a structure that stores terms and implements hash consing.

pub mod advanced;
mod storage;

use super::{Binder, Operator, Rc, Sort, Term};
use crate::ast::{Constant, ParamOperator};
use indexmap::{IndexMap, IndexSet};
use rug::Integer;
use storage::Storage;

pub trait TermPool {
    /// Returns the term corresponding to the boolean constant `true`.
    fn bool_true(&mut self) -> Rc<Term> {
        self.bool_constant(true)
    }

    /// Returns the term corresponding to the boolean constant `false`.
    fn bool_false(&mut self) -> Rc<Term> {
        self.bool_constant(false)
    }

    /// Returns the term corresponding to the boolean constant determined by `value`.
    fn bool_constant(&mut self, value: bool) -> Rc<Term> {
        self.add(Term::new_bool(value))
    }

    /// Takes a term and returns a possibly newly allocated `Rc` that references it.
    ///
    /// If the term was not originally in the term pool, it is added to it. Otherwise, this method
    /// just returns an `Rc` pointing to the existing allocation. This method also computes the
    /// term's sort, and adds it to the sort cache.
    fn add(&mut self, term: Term) -> Rc<Term>;
    /// Takes a vector of terms and calls [`TermPool::add`] on each.
    fn add_all(&mut self, terms: Vec<Term>) -> Vec<Rc<Term>> {
        terms.into_iter().map(|t| self.add(t)).collect()
    }
    /// Returns the sort of the given term.
    ///
    /// This method assumes that the sorts of any subterms have already been checked, and are
    /// correct. If `term` is itself a sort, this simply returns that sort.
    fn sort(&self, term: &Rc<Term>) -> Rc<Term>;
    /// Returns an `IndexSet` containing all the free variables in the given term.
    ///
    /// This method uses a cache, so there is no additional cost to computing the free variables of
    /// a term multiple times.
    fn free_vars(&mut self, term: &Rc<Term>) -> IndexSet<Rc<Term>>;
}

/// A structure to store and manage all allocated terms.
///
/// You can add a `Term` to the pool using [`PrimitivePool::add`], which will return an `Rc<Term>`. This
/// struct ensures that, if two equal terms are added to a pool, they will be in the same
/// allocation. This invariant allows terms to be safely compared and hashed by reference, instead
/// of by value (see [`Rc`]).
///
/// This struct also provides other utility methods, like computing the sort of a term (see
/// [`PrimitivePool::sort`]) or its free variables (see [`PrimitivePool::free_vars`]).
#[derive(Debug, Default)]
pub struct PrimitivePool {
    pub(crate) storage: Storage,
    pub(crate) free_vars_cache: IndexMap<Rc<Term>, IndexSet<Rc<Term>>>,
    pub(crate) sorts_cache: IndexMap<Rc<Term>, Rc<Term>>,
}

impl PrimitivePool {
    /// Constructs a new `TermPool`. This new pool will already contain the boolean constants `true`
    /// and `false`, as well as the `Bool` sort.
    pub fn new() -> Self {
        Self::default()
    }

    /// Computes the sort of a term and adds it to the sort cache.
    fn compute_sort(&mut self, term: &Rc<Term>) -> Rc<Term> {
        if let Some(sort) = self.sorts_cache.get(term) {
            return sort.clone();
        }

        let result: Sort = match term.as_ref() {
            Term::Const(c) => match c {
                Constant::Integer(_) => Sort::Int,
                Constant::Real(_) => Sort::Real,
                Constant::String(_) => Sort::String,
                Constant::BitVec(_, w) => Sort::BitVec(w.clone()),
            },
            Term::Var(_, sort) => sort.as_sort().unwrap().clone(),
            Term::Op(op, args) => match op {
                Operator::True
                | Operator::False
                | Operator::Not
                | Operator::Implies
                | Operator::And
                | Operator::Or
                | Operator::Xor
                | Operator::Equals
                | Operator::Distinct
                | Operator::LessThan
                | Operator::GreaterThan
                | Operator::LessEq
                | Operator::GreaterEq
                | Operator::IsInt
                | Operator::StrLessThan
                | Operator::StrLessEq
                | Operator::PrefixOf
                | Operator::SuffixOf
                | Operator::Contains
                | Operator::StrIsDigit
                | Operator::StrInRe
                | Operator::BvULt
                | Operator::BvULe
                | Operator::BvUGt
                | Operator::BvUGe
                | Operator::BvSLt
                | Operator::BvSLe
                | Operator::BvSGt
                | Operator::BvSGe
                | Operator::BvShl
                | Operator::BvLShr 
                | Operator::Cl
                | Operator::Delete
                => Sort::Bool,
                Operator::BvAdd
                | Operator::BvSub
                | Operator::BvNot
                | Operator::BvNeg
                | Operator::BvNAnd
                | Operator::BvNOr
                | Operator::BvAnd
                | Operator::BvOr
                | Operator::BvUDiv
                | Operator::BvURem
                | Operator::BvXor
                | Operator::BvXNor
                | Operator::BvMul
                | Operator::BvSDiv
                | Operator::BvSRem
                | Operator::BvSMod
                | Operator::BvAShr => {
                    let Sort::BitVec(width) =
                        self.compute_sort(&args[0]).as_sort().unwrap().clone()
                    else {
                        unreachable!()
                    };
                    Sort::BitVec(width)
                }
                Operator::BvComp => Sort::BitVec(Integer::ONE.into()),
                Operator::BvBbTerm => Sort::BitVec(Integer::from(args.len())),
                Operator::BvConcat => {
                    let mut total_width = Integer::ZERO;
                    for arg in args {
                        let Sort::BitVec(arg_width) =
                            self.compute_sort(arg).as_sort().unwrap().clone()
                        else {
                            unreachable!()
                        };
                        total_width += arg_width;
                    }
                    Sort::BitVec(total_width)
                }
                Operator::Ite => self.compute_sort(&args[1]).as_sort().unwrap().clone(),
                Operator::Add | Operator::Sub | Operator::Mult => {
                    if args
                        .iter()
                        .any(|a| self.compute_sort(a).as_sort().unwrap() == &Sort::Real)
                    {
                        Sort::Real
                    } else {
                        Sort::Int
                    }
                }
                Operator::RealDiv | Operator::ToReal => Sort::Real,
                Operator::IntDiv | Operator::Mod | Operator::Abs | Operator::ToInt => Sort::Int,
                Operator::Select => match self.compute_sort(&args[0]).as_sort().unwrap() {
                    Sort::Array(_, y) => y.as_sort().unwrap().clone(),
                    _ => unreachable!(),
                },
                Operator::Store => self.compute_sort(&args[0]).as_sort().unwrap().clone(),
                Operator::StrLen | Operator::IndexOf | Operator::StrToCode | Operator::StrToInt => {
                    Sort::Int
                }
                Operator::StrConcat
                | Operator::CharAt
                | Operator::Substring
                | Operator::Replace
                | Operator::ReplaceAll
                | Operator::ReplaceRe
                | Operator::ReplaceReAll
                | Operator::StrFromCode
                | Operator::StrFromInt => Sort::String,
                Operator::StrToRe
                | Operator::ReNone
                | Operator::ReAll
                | Operator::ReAllChar
                | Operator::ReConcat
                | Operator::ReUnion
                | Operator::ReIntersection
                | Operator::ReKleeneClosure
                | Operator::ReComplement
                | Operator::ReDiff
                | Operator::ReKleeneCross
                | Operator::ReOption
                | Operator::ReRange => Sort::RegLan,
                Operator::RareList => Sort::RareList,
            },
            Term::App(f, _) => {
                match self.compute_sort(f).as_sort().unwrap() {
                    Sort::Function(sorts) => sorts.last().unwrap().as_sort().unwrap().clone(),
                    _ => unreachable!(), // We assume that the function is correctly sorted
                }
            }
            Term::Sort(_) => Sort::Type,
            Term::Binder(Binder::Forall | Binder::Exists, _, _) => Sort::Bool,
            Term::Binder(Binder::Choice, v, _) => v[0].1.as_sort().unwrap().clone(),
            Term::Binder(Binder::Lambda, bindings, body) => {
                let mut result: Vec<_> =
                    bindings.iter().map(|(_name, sort)| sort.clone()).collect();
                result.push(self.compute_sort(body));
                Sort::Function(result)
            }
            Term::Let(_, inner) => self.compute_sort(inner).as_sort().unwrap().clone(),
            Term::ParamOp { op, op_args, args } => {
                let sort = match op {
                    ParamOperator::BvExtract => {
                        let i = op_args[0].as_integer().unwrap();
                        let j = op_args[1].as_integer().unwrap();
                        Sort::BitVec(i - j + Integer::ONE)
                    }
                    ParamOperator::ZeroExtend | ParamOperator::SignExtend => {
                        let extension_width = op_args[0].as_integer().unwrap();
                        let Sort::BitVec(bv_width) =
                            self.compute_sort(&args[0]).as_sort().unwrap().clone()
                        else {
                            unreachable!()
                        };
                        Sort::BitVec(extension_width + bv_width)
                    }
                    ParamOperator::BvConst => unreachable!(
                        "bv const should be handled by the parser and transfromed into a constant"
                    ),
                    ParamOperator::BvBitOf => Sort::Bool,
                    ParamOperator::RePower | ParamOperator::ReLoop => Sort::RegLan,
                    ParamOperator::ArrayConst => op_args[0].as_sort().unwrap().clone(),
                };
                sort
            }
        };
        let sort = self.storage.add(Term::Sort(result));
        self.sorts_cache.insert(term.clone(), sort);
        self.sorts_cache[term].clone()
    }

    fn add_with_priorities<const N: usize>(
        &mut self,
        term: Term,
        prior_pools: [&PrimitivePool; N],
    ) -> Rc<Term> {
        for p in prior_pools {
            // If this prior pool has the term
            if let Some(entry) = p.storage.get(&term) {
                return entry.clone();
            }
        }
        self.add(term)
    }

    fn sort_with_priorities<const N: usize>(
        &mut self,
        term: &Rc<Term>,
        prior_pools: [&PrimitivePool; N],
    ) -> Rc<Term> {
        for p in prior_pools {
            if let Some(sort) = p.sorts_cache.get(term) {
                return sort.clone();
            }
        }
        self.sorts_cache[term].clone()
    }

    // TODO: Try to workaround the lifetime specifiers and return a ref
    pub fn free_vars_with_priorities<const N: usize>(
        &mut self,
        term: &Rc<Term>,
        prior_pools: [&PrimitivePool; N],
    ) -> IndexSet<Rc<Term>> {
        for p in prior_pools {
            if let Some(set) = p.free_vars_cache.get(term) {
                return set.clone();
            }
        }

        if let Some(set) = self.free_vars_cache.get(term) {
            return set.clone();
        }

        let set = match term.as_ref() {
            Term::App(f, args) => {
                let mut set = self.free_vars_with_priorities(f, prior_pools);
                for a in args {
                    set.extend(self.free_vars_with_priorities(a, prior_pools).into_iter());
                }
                set
            }
            Term::Op(_, args) => {
                let mut set = IndexSet::new();
                for a in args {
                    set.extend(self.free_vars_with_priorities(a, prior_pools).into_iter());
                }
                set
            }
            Term::Binder(_, bindings, inner) => {
                let mut vars = self.free_vars_with_priorities(inner, prior_pools);
                for bound_var in bindings {
                    let term = self.add_with_priorities(bound_var.clone().into(), prior_pools);
                    vars.remove(&term);
                }
                vars
            }
            Term::Let(bindings, inner) => {
                let mut vars = self.free_vars_with_priorities(inner, prior_pools);
                for (var, value) in bindings {
                    let sort = self.sort_with_priorities(value, prior_pools);
                    let term = self.add_with_priorities((var.clone(), sort).into(), prior_pools);
                    vars.remove(&term);
                }
                vars
            }
            Term::Var(..) => {
                let mut set = IndexSet::with_capacity(1);
                set.insert(term.clone());
                set
            }
            Term::Const(_) | Term::Sort(_) => IndexSet::new(),
            Term::ParamOp { op: _, op_args: _, args } => {
                let mut set = IndexSet::new();
                for a in args {
                    set.extend(self.free_vars_with_priorities(a, prior_pools).into_iter());
                }
                set
            }
        };
        self.free_vars_cache.insert(term.clone(), set);
        self.free_vars_cache.get(term).unwrap().clone()
    }
}

impl TermPool for PrimitivePool {
    fn add(&mut self, term: Term) -> Rc<Term> {
        let term = self.storage.add(term);
        self.compute_sort(&term);
        term
    }

    fn sort(&self, term: &Rc<Term>) -> Rc<Term> {
        self.sorts_cache[term].clone()
    }

    fn free_vars(&mut self, term: &Rc<Term>) -> IndexSet<Rc<Term>> {
        self.free_vars_with_priorities(term, [])
    }
}
