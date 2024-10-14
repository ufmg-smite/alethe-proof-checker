//! This module implements less strict definitions of equality for terms. In particular, it
//! contains two definitions of equality that differ from `PartialEq`:
//!
//! - `polyeq` considers `=` terms that are reflections of each other as equal, meaning the terms
//! `(= a b)` and `(= b a)` are considered equal by this method.
//!
//! - `alpha_equiv` compares terms by alpha-equivalence, meaning it implements equality of terms
//! modulo renaming of bound variables.

use rug::Rational;

use super::{
    AnchorArg, BindingList, Constant, Operator, ProofCommand, ProofStep, Rc, Sort, Subproof, Term,
};
use crate::utils::HashMapStack;
use std::time::{Duration, Instant};

/// An helper enum that allow a construction of lists with easy differentiation over the nature of the term
/// (String constant or other). Therefore, is easy to manipulate, attach and detach terms of lists of
/// this type, making easy the process of comparing equal Strings modulo the String concatenation.
#[derive(Debug, Clone)]
enum Concat {
    Constant(String),
    Term(Rc<Term>),
}

/// A function that receives the list of arguments of an operation term and returns that same list with every
/// argument encapsulated by the constructors of the Concat enum . This will be helpful to process the terms and
/// compare if a String constant and a String concatenation are equivalents.
fn to_concat(args: &[Rc<Term>]) -> Vec<Concat> {
    args.iter()
        .map(|arg| match arg.as_ref() {
            Term::Const(Constant::String(s)) => Concat::Constant(s.clone()),
            _ => Concat::Term(arg.clone()),
        })
        .collect()
}

/// A trait that represents objects that can be compared for equality modulo reordering of
/// equalities or alpha equivalence.
pub trait PolyeqComparable {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool;
}

/// Computes whether the two given terms are equal, modulo reordering of equalities.
///
/// That is, for this function, `=` terms that are reflections of each other are considered as
/// equal, meaning terms like `(and p (= a b))` and `(and p (= b a))` are considered equal.
///
/// This function records how long it takes to run, and adds that duration to the `time` argument.
pub fn polyeq(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> bool {
    Polyeq::new().mod_reordering(true).eq_with_time(a, b, time)
}

/// Similar to `polyeq`, but instead compares terms for alpha equivalence.
///
/// This means that two terms which are the same, except for the renaming of a bound variable, are
/// considered equivalent. This functions still considers equality modulo reordering of equalities.
/// For example, this function will consider the terms `(forall ((x Int)) (= x 0))` and `(forall ((y
/// Int)) (= 0 y))` as equivalent.
///
/// This function records how long it takes to run, and adds that duration to the `time` argument.
pub fn alpha_equiv(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> bool {
    Polyeq::new()
        .mod_reordering(true)
        .alpha_equiv(true)
        .eq_with_time(a, b, time)
}

/// Configuration for a `Polyeq`.
///
/// - If `is_mod_reordering` is `true`, the comparator will compare terms modulo reordering of
/// equalities.
//  - If `is_alpha_equivalence` is `true`, the comparator will compare terms for alpha
/// equivalence.
/// - If `is_mod_nary` is `true`, the comparator will compare terms modulo the expansion of
/// n-ary operators.
/// - If `is_mod_string_concat` is `true`, the comparator will compare terms modulo the collection of
/// String constants arguments in the String concatenation.
#[derive(Default)]
pub struct PolyeqConfig {
    pub is_mod_reordering: bool,
    pub is_alpha_equivalence: bool,
    pub is_mod_nary: bool,
    pub is_mod_string_concat: bool,
}

impl PolyeqConfig {
    pub fn new() -> Self {
        Self::default()
    }
}

/// A configurable comparator for polyequality and alpha equivalence.
pub struct Polyeq {
    // In order to check alpha-equivalence, we can't use a simple global cache. For instance, let's
    // say we are comparing the following terms for alpha equivalence:
    // ```
    //     a := (and
    //         (forall ((x Int) (y Int)) (< x y))
    //         (forall ((x Int) (y Int)) (< x y))
    //     )
    //     b := (and
    //         (forall ((x Int) (y Int)) (< x y))
    //         (forall ((y Int) (x Int)) (< x y))
    //     )
    // ```
    // When comparing the first argument of each term, `(forall ((x Int) (y Int)) (< x y))`,
    // `(< x y)` will become `(< $0 $1)` for both `a` and `b`, using De Bruijn indices. We will see
    // that they are equal, and add the entry `((< x y), (< x y))` to the cache. However, when we
    // are comparing the second argument of each term, `(< x y)` will again be `(< $0 $1)` in `a`,
    // but it will be `(< $1 $0)` in `b`. If we just rely on the cache, we will incorrectly
    // determine that `a` and `b` are alpha-equivalent.  To account for that, we use a more
    // complicated caching system, based on a `HashMapStack`. We push a new scope every time we
    // enter a binder term, and pop it as we exit. This unfortunately means that equalities derived
    // inside a binder term can't be reused outside of it, degrading performance. If we are not
    // checking for alpha-equivalence, we never push an additional scope to this `HashMapStack`,
    // meaning it functions as a simple hash map.
    cache: HashMapStack<(Rc<Term>, Rc<Term>), ()>,
    is_mod_reordering: bool,
    de_bruijn_map: Option<DeBruijnMap>,
    is_mod_nary: bool,
    is_mod_string_concat: bool,

    current_depth: usize,
    max_depth: usize,
}

impl Default for Polyeq {
    fn default() -> Self {
        Self::new()
    }
}

impl Polyeq {
    /// Constructs a new `Polyeq` with default configuration.
    pub fn new() -> Self {
        Self::with_config(PolyeqConfig::new())
    }

    /// Constructs a new `Polyeq`.
    pub fn with_config(config: PolyeqConfig) -> Self {
        Self {
            cache: HashMapStack::new(),
            is_mod_reordering: config.is_mod_reordering,
            de_bruijn_map: config.is_alpha_equivalence.then(DeBruijnMap::new),
            is_mod_nary: config.is_mod_nary,
            is_mod_string_concat: config.is_mod_string_concat,
            current_depth: 0,
            max_depth: 0,
        }
    }

    pub fn mod_reordering(mut self, value: bool) -> Self {
        self.is_mod_reordering = value;
        self
    }

    pub fn alpha_equiv(mut self, value: bool) -> Self {
        self.de_bruijn_map = value.then(DeBruijnMap::new);
        self
    }

    pub fn mod_nary(mut self, value: bool) -> Self {
        self.is_mod_nary = value;
        self
    }

    pub fn mod_string_concat(mut self, value: bool) -> Self {
        self.is_mod_string_concat = value;
        self
    }

    pub fn eq<T>(&mut self, a: &T, b: &T) -> bool
    where
        T: PolyeqComparable + ?Sized,
    {
        PolyeqComparable::eq(self, a, b)
    }

    pub fn eq_with_time<T>(&mut self, a: &T, b: &T, time: &mut Duration) -> bool
    where
        T: PolyeqComparable + ?Sized,
    {
        let start = Instant::now();
        let result = self.eq(a, b);
        *time += start.elapsed();
        result
    }

    pub fn max_depth(&self) -> usize {
        self.max_depth
    }

    fn compare_binder(
        &mut self,
        a_binds: &BindingList,
        b_binds: &BindingList,
        a_inner: &Rc<Term>,
        b_inner: &Rc<Term>,
    ) -> bool {
        if let Some(de_bruijn_map) = self.de_bruijn_map.as_mut() {
            // First, we push new scopes into the De Bruijn map and the cache stack
            de_bruijn_map.push();
            self.cache.push_scope();

            // Then, we check that the binding lists and the inner terms are equivalent
            for (a_var, b_var) in a_binds.iter().zip(b_binds.iter()) {
                if !self.eq(&a_var.1, &b_var.1) {
                    // We must remember to pop the frames from the De Bruijn map and cache stack
                    // here, so as not to leave them in a corrupted state
                    self.de_bruijn_map.as_mut().unwrap().pop();
                    self.cache.pop_scope();
                    return false;
                }
                // We also insert each variable in the binding lists into the De Bruijn map
                self.de_bruijn_map
                    .as_mut()
                    .unwrap()
                    .insert(a_var.0.clone(), b_var.0.clone());
            }
            let result = self.eq(a_inner, b_inner);

            // Finally, we pop the scopes we pushed
            self.de_bruijn_map.as_mut().unwrap().pop();
            self.cache.pop_scope();

            result
        } else {
            self.eq(a_binds, b_binds) && self.eq(a_inner, b_inner)
        }
    }

    fn compare_op(
        &mut self,
        op_a: Operator,
        args_a: &[Rc<Term>],
        op_b: Operator,
        args_b: &[Rc<Term>],
    ) -> bool {
        // Modulo string concatenation
        if self.is_mod_string_concat {
            let concat_args_a: Vec<Concat> = to_concat(args_a);
            let concat_args_b: Vec<Concat> = to_concat(args_b);
            return self.compare_strings(concat_args_a, concat_args_b);
        }

        // Modulo reordering of equalities
        if self.is_mod_reordering {
            if let (Operator::Equals, [a_1, a_2], Operator::Equals, [b_1, b_2]) =
                (op_a, args_a, op_b, args_b)
            {
                // If the term is an equality of two terms, we also check if they would be
                // equal if one of them was flipped
                return self.eq(&(a_1, a_2), &(b_1, b_2)) || self.eq(&(a_1, a_2), &(b_2, b_1));
            }
        }

        // Modulo n-ary expansion
        if self.is_mod_nary {
            if op_a != op_b {
                // TODO: check pairwise case
                return if nary_case(op_a) == Some(NaryCase::Chainable) {
                    op_b == Operator::And && self.compare_chainable(op_a, args_a, args_b)
                } else if nary_case(op_b) == Some(NaryCase::Chainable) {
                    op_a == Operator::And && self.compare_chainable(op_b, args_b, args_a)
                } else {
                    false
                };
            } else if args_a.len() != args_b.len() {
                let case = nary_case(op_a);
                return matches!(case, Some(NaryCase::RightAssoc | NaryCase::LeftAssoc))
                    && self.compare_assoc(op_a, args_a, args_b);
            };
        }

        // General case
        op_a == op_b && self.eq(args_a, args_b)
    }

    fn compare_chainable(&mut self, op: Operator, args: &[Rc<Term>], chain: &[Rc<Term>]) -> bool {
        if args.len() != chain.len() + 1 {
            return false;
        }
        args.windows(2)
            .zip(chain.iter())
            .all(|(window, chain_term)| {
                let (a, b) = (&window[0], &window[1]);
                match chain_term.as_ref() {
                    Term::Op(chain_op, args) if *chain_op == op && args.len() == 2 => {
                        self.eq(a, &args[0]) && self.eq(b, &args[1])
                    }
                    _ => false,
                }
            })
    }

    fn compare_assoc(&mut self, op: Operator, left: &[Rc<Term>], right: &[Rc<Term>]) -> bool {
        fn split(args: &[Rc<Term>], is_right: bool) -> (&Rc<Term>, &[Rc<Term>]) {
            match args {
                [] | [_] => unreachable!(),
                [first, rest @ ..] if is_right => (first, rest),
                [rest @ .., last] => (last, rest),
            }
        }

        fn flatten_if_singleton(tail: &[Rc<Term>], op: Operator) -> Option<&[Rc<Term>]> {
            let [term] = tail else {
                return None;
            };
            let (term_op, args) = term.as_op()?;
            if term_op == op {
                Some(args)
            } else {
                None
            }
        }

        match (left.len(), right.len()) {
            (1, 1) => return self.eq(&left[0], &right[0]),
            (1, _) | (_, 1) => return false,
            _ => (),
        }

        let is_right = nary_case(op) == Some(NaryCase::RightAssoc);

        let (left_head, mut left_tail) = split(left, is_right);
        let (right_head, mut right_tail) = split(right, is_right);

        if !self.eq(left_head, right_head) {
            return false;
        }

        left_tail = flatten_if_singleton(left_tail, op).unwrap_or(left_tail);
        right_tail = flatten_if_singleton(right_tail, op).unwrap_or(right_tail);

        self.compare_assoc(op, left_tail, right_tail)
    }

    fn remainder(&mut self, a: Vec<Concat>, b: Vec<Concat>) -> (Vec<Concat>, Vec<Concat>) {
        match (a.first(), b.first()) {
            (None | Some(_), None) | (None, Some(_)) => (a, b),
            (Some(a_head), Some(b_head)) => match (a_head, b_head) {
                (Concat::Constant(a_constant), Concat::Constant(b_constant)) => {
                    let prefix_length = std::cmp::min(a_constant.len(), b_constant.len());
                    for i in 0..prefix_length {
                        if a_constant.chars().nth(i).unwrap() != b_constant.chars().nth(i).unwrap()
                        {
                            return (a, b);
                        }
                    }
                    let a_const_rem = &a_constant[prefix_length..];
                    let b_const_rem = &b_constant[prefix_length..];
                    let mut new_a = a[1..].to_vec();
                    let mut new_b = b[1..].to_vec();
                    if !a_const_rem.is_empty() {
                        new_a.insert(0, Concat::Constant(a_const_rem.to_owned()));
                    }
                    if !b_const_rem.is_empty() {
                        new_b.insert(0, Concat::Constant(b_const_rem.to_owned()));
                    }
                    self.remainder(new_a, new_b)
                }
                (Concat::Constant(constant), Concat::Term(term)) => match term.as_ref() {
                    Term::Op(Operator::StrConcat, args) => {
                        let concat_args: Vec<Concat> = to_concat(args);
                        let (constant_rem, concat_rem) = self.remainder(a.clone(), concat_args);
                        let mut new_b = b[1..].to_vec();
                        for c in concat_rem.iter().rev() {
                            new_b.insert(0, c.clone());
                        }
                        self.remainder(constant_rem, new_b)
                    }
                    _ => {
                        if constant.is_empty() {
                            return self.remainder(a[1..].to_vec(), b);
                        }
                        (a, b)
                    }
                },
                (Concat::Term(term), Concat::Constant(constant)) => match term.as_ref() {
                    Term::Op(Operator::StrConcat, args) => {
                        let concat_args: Vec<Concat> = to_concat(args);
                        let (concat_rem, constant_rem) = self.remainder(concat_args, b.clone());
                        let mut new_a = a[1..].to_vec();
                        for c in concat_rem.iter().rev() {
                            new_a.insert(0, c.clone());
                        }
                        self.remainder(new_a, constant_rem)
                    }
                    _ => {
                        if constant.is_empty() {
                            return self.remainder(a, b[1..].to_vec());
                        }
                        (a, b)
                    }
                },
                (Concat::Term(a_term), Concat::Term(b_term)) => {
                    match (a_term.as_ref(), b_term.as_ref()) {
                        (
                            Term::Op(Operator::StrConcat, a_args),
                            Term::Op(Operator::StrConcat, b_args),
                        ) => {
                            let concat_a_args: Vec<Concat> = to_concat(a_args);
                            let concat_b_args: Vec<Concat> = to_concat(b_args);
                            let (concat_a_rem, concat_b_rem) =
                                self.remainder(concat_a_args, concat_b_args);
                            let mut new_a = a[1..].to_vec();
                            let mut new_b = b[1..].to_vec();
                            for c in concat_a_rem.iter().rev() {
                                new_a.insert(0, c.clone());
                            }
                            for c in concat_b_rem.iter().rev() {
                                new_b.insert(0, c.clone());
                            }
                            self.remainder(new_a, new_b)
                        }
                        (Term::Op(Operator::StrConcat, a_args), _) => {
                            if self.eq(&a_args[0], b_term) {
                                let concat_a_rem: Vec<Concat> = to_concat(&a_args[1..]);
                                let mut new_a = a[1..].to_vec();
                                for c in concat_a_rem.iter().rev() {
                                    new_a.insert(0, c.clone());
                                }
                                let new_b = b[1..].to_vec();
                                self.remainder(new_a, new_b)
                            } else {
                                (a, b)
                            }
                        }
                        (_, Term::Op(Operator::StrConcat, b_args)) => {
                            if self.eq(&b_args[0], a_term) {
                                let new_a = a[1..].to_vec();
                                let concat_b_rem: Vec<Concat> = to_concat(&b_args[1..]);
                                let mut new_b = b[1..].to_vec();
                                for c in concat_b_rem.iter().rev() {
                                    new_b.insert(0, c.clone());
                                }
                                self.remainder(new_a, new_b)
                            } else {
                                (a, b)
                            }
                        }
                        _ => {
                            if self.eq(a_term, b_term) {
                                let new_a = a[1..].to_vec();
                                let new_b = b[1..].to_vec();
                                self.remainder(new_a, new_b)
                            } else {
                                (a, b)
                            }
                        }
                    }
                }
            },
        }
    }

    fn compare_strings(&mut self, a: Vec<Concat>, b: Vec<Concat>) -> bool {
        matches!(self.remainder(a, b), (rem_a, rem_b) if rem_a.is_empty() && rem_b.is_empty())
    }
}

impl PolyeqComparable for Rc<Term> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        // In general, if the two `Rc`s are directly equal, we can return `true`.
        //
        // However, if we are checking for alpha-equivalence, identical terms may be considered
        // different if the bound variables in them have different meanings. For example, in the
        // terms `(forall ((x Int) (y Int)) (< x y))` and `(forall ((y Int) (x Int)) (< x y))`,
        // even though both instances of `(< x y)` are identical, they are not alpha-equivalent.
        //
        // To account for that, if we are checking for alpha-equivalence and have encountered at
        // least one binder, we don't apply this optimization
        let possibly_renamed = comp.de_bruijn_map.as_ref().is_some_and(|m| !m.is_empty());
        if !possibly_renamed && a == b {
            return true;
        }

        // We first check the cache to see if these terms were already determined to be equal
        if comp.cache.get(&(a.clone(), b.clone())).is_some() {
            return true;
        }

        comp.current_depth += 1;
        comp.max_depth = std::cmp::max(comp.max_depth, comp.current_depth);
        let result = comp.eq(a.as_ref(), b.as_ref());
        if result {
            comp.cache.insert((a.clone(), b.clone()), ());
        }
        comp.current_depth -= 1;
        result
    }
}

impl PolyeqComparable for Term {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Term::Const(a), Term::Const(b)) => a == b,
            (Term::Var(a, a_sort), Term::Var(b, b_sort)) if comp.de_bruijn_map.is_some() => {
                // If we are checking for alpha-equivalence, and we encounter two variables, we
                // check that they are equivalent using the De Bruijn map
                if let Some(db) = comp.de_bruijn_map.as_mut() {
                    db.compare(a, b) && comp.eq(a_sort, b_sort)
                } else {
                    a == b && comp.eq(a_sort, b_sort)
                }
            }
            (Term::App(f_a, args_a), Term::App(f_b, args_b)) => {
                comp.eq(f_a, f_b) && comp.eq(args_a, args_b)
            }
            (
                Term::ParamOp {
                    op: op_a,
                    op_args: op_args_a,
                    args: args_a,
                },
                Term::ParamOp {
                    op: op_b,
                    op_args: op_args_b,
                    args: args_b,
                },
            ) => op_a == op_b && op_args_a == op_args_b && comp.eq(args_a, args_b),

            (Term::Op(op_a, args_a), Term::Op(op_b, args_b)) => {
                comp.compare_op(*op_a, args_a, *op_b, args_b)
            }
            (Term::Sort(a), Term::Sort(b)) => comp.eq(a, b),
            (Term::Binder(q_a, binds_a, a), Term::Binder(q_b, binds_b, b)) => {
                q_a == q_b && comp.compare_binder(binds_a, binds_b, a, b)
            }
            (Term::Let(binds_a, a), Term::Let(binds_b, b)) => {
                comp.compare_binder(binds_a, binds_b, a, b)
            }
            (Term::Const(Constant::Real(r)), Term::Op(Operator::RealDiv, args)) => {
                // if a is a rational and b a division literal, check
                // if they are the same
                match (args[0].as_ref(), args[1].as_ref()) {
                    (Term::Const(Constant::Real(r1)), Term::Const(Constant::Real(r2)))
                        if r1.is_integer() && r2.is_integer() =>
                    {
                        Rational::from((r1.numer(), r2.numer())) == r.clone()
                    }
                    _ => false,
                }
            }
            (Term::Op(Operator::RealDiv, args), Term::Const(Constant::Real(r))) => {
                // if a is a rational and b a division literal, check
                // if they are the same
                match (args[0].as_ref(), args[1].as_ref()) {
                    (Term::Const(Constant::Real(r1)), Term::Const(Constant::Real(r2)))
                        if r1.is_integer() && r2.is_integer() =>
                    {
                        Rational::from((r1.numer(), r2.numer())) == r.clone()
                    }
                    _ => false,
                }
            }
            (Term::Const(Constant::Integer(i1)), Term::Op(Operator::Sub, args))
            | (Term::Op(Operator::Sub, args), Term::Const(Constant::Integer(i1)))
                if i1.is_negative() && args.len() == 1 =>
            {
                if let Term::Const(Constant::Integer(i2)) = args[0].as_ref() {
                    i1.clone().abs() == i2.clone()
                } else {
                    false
                }
            }
            (Term::Op(Operator::Sub, args), Term::Const(Constant::Real(r)))
            | (Term::Const(Constant::Real(r)), Term::Op(Operator::Sub, args))
                if r.is_negative() && args.len() == 1 =>
            {
                match args[0].as_ref() {
                    Term::Op(Operator::RealDiv, sub_args) => {
                        match (sub_args[0].as_ref(), sub_args[1].as_ref()) {
                            (Term::Const(Constant::Real(r1)), Term::Const(Constant::Real(r2)))
                                if r1.is_integer() && r2.is_integer() =>
                            {
                                Rational::from((r1.numer(), r2.numer())) == r.clone().abs()
                            }
                            _ => false,
                        }
                    }
                    Term::Const(Constant::Real(r1)) => r1.clone() == r.clone().abs(),
                    _ => false,
                }
            }
            _ => {
                if comp.is_mod_string_concat {
                    return match (a, b) {
                        (
                            Term::Op(Operator::StrConcat, args_a),
                            Term::Const(Constant::String(b)),
                        ) => {
                            let concat_args_a: Vec<Concat> = to_concat(args_a);
                            let concat_args_b = vec![Concat::Constant(b.clone())];
                            comp.compare_strings(concat_args_a, concat_args_b)
                        }
                        (
                            Term::Const(Constant::String(a)),
                            Term::Op(Operator::StrConcat, args_b),
                        ) => {
                            let concat_args_a = vec![Concat::Constant(a.clone())];
                            let concat_args_b: Vec<Concat> = to_concat(args_b);
                            comp.compare_strings(concat_args_a, concat_args_b)
                        }
                        _ => false,
                    };
                }
                false
            }
        }
    }
}

impl PolyeqComparable for BindingList {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(&a.0, &b.0)
    }
}

impl PolyeqComparable for Sort {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => comp.eq(sorts_a, sorts_b),
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => a == b && comp.eq(sorts_a, sorts_b),
            (Sort::Bool, Sort::Bool)
            | (Sort::Int, Sort::Int)
            | (Sort::Real, Sort::Real)
            | (Sort::String, Sort::String)
            | (Sort::RegLan, Sort::RegLan)
            | (Sort::RareList, Sort::RareList)
            | (Sort::Type, Sort::Type) => true,
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                comp.eq(x_a, x_b) && comp.eq(y_a, y_b)
            }
            (Sort::BitVec(a), Sort::BitVec(b)) => a == b,
            _ => false,
        }
    }
}

impl<T: PolyeqComparable> PolyeqComparable for &T {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(*a, *b)
    }
}

impl<T: PolyeqComparable> PolyeqComparable for [T] {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| comp.eq(a, b))
    }
}

impl<T: PolyeqComparable> PolyeqComparable for Vec<T> {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(a.as_slice(), b.as_slice())
    }
}

impl<T: PolyeqComparable, U: PolyeqComparable> PolyeqComparable for (T, U) {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(&a.0, &b.0) && comp.eq(&a.1, &b.1)
    }
}

impl PolyeqComparable for String {
    fn eq(_: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a == b
    }
}

impl PolyeqComparable for AnchorArg {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (AnchorArg::Variable(a), AnchorArg::Variable(b)) => comp.eq(a, b),
            (AnchorArg::Assign(a_name, a_value), AnchorArg::Assign(b_name, b_value)) => {
                a_name == b_name && comp.eq(a_value, b_value)
            }
            _ => false,
        }
    }
}

impl PolyeqComparable for ProofCommand {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (
                ProofCommand::Assume { id: a_id, term: a_term },
                ProofCommand::Assume { id: b_id, term: b_term },
            ) => a_id == b_id && comp.eq(a_term, b_term),
            (ProofCommand::Step(a), ProofCommand::Step(b)) => comp.eq(a, b),
            (ProofCommand::Subproof(a), ProofCommand::Subproof(b)) => comp.eq(a, b),
            _ => false,
        }
    }
}

impl PolyeqComparable for ProofStep {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        a.id == b.id
            && comp.eq(&a.clause, &b.clause)
            && a.rule == b.rule
            && a.premises == b.premises
            && comp.eq(&a.args, &b.args)
            && a.discharge == b.discharge
    }
}

impl PolyeqComparable for Subproof {
    fn eq(comp: &mut Polyeq, a: &Self, b: &Self) -> bool {
        comp.eq(&a.commands, &b.commands) && comp.eq(&a.args, &b.args)
    }
}

struct DeBruijnMap {
    // To check for alpha-equivalence, we make use of De Bruijn indices. The idea is to map each
    // bound variable to an integer depending on the order in which they were bound. As we compare
    // the two terms, if we encounter two bound variables, we need only to check if the associated
    // integers are equal, and the actual names of the variables are irrelevant.
    //
    // Normally, the index selected for a given appearance of a variable is the number of bound
    // variables introduced between that variable and its appearance. That is, the term
    //     `(forall ((x Int)) (and (exists ((y Int)) (> x y)) (> x 5)))`
    // would be represented using De Bruijn indices like this:
    //     `(forall ((x Int)) (and (exists ((y Int)) (> $1 $0)) (> $0 5)))`
    // This has a few annoying properties, like the fact that the same bound variable can receive
    // different indices in different appearances (in the example, `x` appears as both `$0` and
    // `$1`). To simplify the implementation, we revert the order of the indices, such that each
    // variable appearance is assigned the index of the binding of that variable. That is, all
    // appearances of the first bound variable are assigned `$0`, all appearances of the variable
    // that is bound second are assigned `$1`, etc. The given term would then be represented like
    // this:
    //     `(forall ((x Int)) (and (exists ((y Int)) (> $0 $1)) (> $0 5)))`
    indices: (HashMapStack<String, usize>, HashMapStack<String, usize>),

    // Holds the count of how many variables were bound before each depth
    counter: Vec<usize>,
}

impl DeBruijnMap {
    fn new() -> Self {
        Self {
            indices: (HashMapStack::new(), HashMapStack::new()),
            counter: vec![0],
        }
    }

    fn is_empty(&self) -> bool {
        self.indices.0.is_empty() && self.indices.1.is_empty()
    }

    fn push(&mut self) {
        self.indices.0.push_scope();
        self.indices.1.push_scope();
        let current = *self.counter.last().unwrap();
        self.counter.push(current);
    }

    fn pop(&mut self) {
        self.indices.0.pop_scope();
        self.indices.1.pop_scope();

        // If we successfully popped the scopes from the indices stacks, that means that there was
        // at least one scope, so we can safely pop from the counter stack as well
        self.counter.pop();
    }

    fn insert(&mut self, a: String, b: String) {
        let current = self.counter.last_mut().unwrap();
        self.indices.0.insert(a, *current);
        self.indices.1.insert(b, *current);
        *current += 1;
    }

    fn compare(&self, a: &str, b: &str) -> bool {
        match (self.indices.0.get(a), self.indices.1.get(b)) {
            // If both a and b are free variables, they need to have the same name
            (None, None) => a == b,

            // If they are both bound variables, they need to have the same De Bruijn indices
            (Some(a), Some(b)) => a == b,

            // If one of them is bound and the other is free, they are not equal
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NaryCase {
    Chainable,
    RightAssoc,
    LeftAssoc,
    Pairwise,
}

fn nary_case(op: Operator) -> Option<NaryCase> {
    // We avoid using the wildcard pattern (i.e. `_`) in this match expression so that when someone
    // adds a new operator, they are reminded to add it to this match
    match op {
        // Logical
        Operator::Implies => Some(NaryCase::RightAssoc),
        Operator::And | Operator::Or | Operator::Xor => Some(NaryCase::LeftAssoc),
        Operator::Equals => Some(NaryCase::Chainable),
        Operator::Distinct => Some(NaryCase::Pairwise),
        Operator::True | Operator::False | Operator::Not | Operator::Ite => None,

        // Integers/Reals
        Operator::Add | Operator::Sub | Operator::Mult | Operator::IntDiv | Operator::RealDiv => {
            Some(NaryCase::LeftAssoc)
        }
        Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
            Some(NaryCase::Chainable)
        }
        Operator::Mod | Operator::Abs | Operator::ToReal | Operator::ToInt | Operator::IsInt => {
            None
        }

        // Arrays
        Operator::Select | Operator::Store => None,

        // Strings
        Operator::StrConcat
        | Operator::StrLessThan
        | Operator::StrLessEq
        | Operator::ReConcat
        | Operator::ReUnion
        | Operator::ReIntersection
        | Operator::ReDiff => Some(NaryCase::LeftAssoc),
        Operator::StrLen
        | Operator::CharAt
        | Operator::Substring
        | Operator::PrefixOf
        | Operator::SuffixOf
        | Operator::Contains
        | Operator::IndexOf
        | Operator::Replace
        | Operator::ReplaceAll
        | Operator::ReplaceRe
        | Operator::ReplaceReAll
        | Operator::StrIsDigit
        | Operator::StrToCode
        | Operator::StrFromCode
        | Operator::StrToInt
        | Operator::StrFromInt
        | Operator::StrToRe
        | Operator::StrInRe
        | Operator::ReNone
        | Operator::ReAll
        | Operator::ReAllChar
        | Operator::ReKleeneClosure
        | Operator::ReComplement
        | Operator::ReKleeneCross
        | Operator::ReOption
        | Operator::ReRange => None,

        // Bitvectors
        Operator::BvAnd | Operator::BvOr | Operator::BvAdd | Operator::BvMul => {
            Some(NaryCase::LeftAssoc)
        }
        Operator::BvNot
        | Operator::BvNeg
        | Operator::BvUDiv
        | Operator::BvURem
        | Operator::BvShl
        | Operator::BvLShr
        | Operator::BvULt
        | Operator::BvConcat
        | Operator::BvNAnd
        | Operator::BvNOr
        | Operator::BvXor
        | Operator::BvXNor
        | Operator::BvComp
        | Operator::BvSub
        | Operator::BvSDiv
        | Operator::BvSRem
        | Operator::BvSMod
        | Operator::BvAShr
        | Operator::BvULe
        | Operator::BvUGt
        | Operator::BvUGe
        | Operator::BvSLt
        | Operator::BvSLe
        | Operator::BvSGt
        | Operator::BvSGe
        | Operator::BvBbTerm
        | Operator::RareList => None,
    }
}
