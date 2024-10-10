//! Algorithms for creating and applying capture-avoiding substitutions over terms.

use super::{Binder, BindingList, Rc, Sort, SortedVar, Term, TermPool};
use indexmap::{IndexMap, IndexSet};
use thiserror::Error;

/// The error type for errors when constructing or applying substitutions.
#[derive(Debug, PartialEq, Eq, Error)]
pub enum SubstitutionError {
    /// A term in the left-hand side of the substitution was not a variable.
    #[error("term in the left-hand side of substitution is not a variable: '{0}'")]
    NotAVariable(Rc<Term>),

    /// One of the mappings in the substitution was mapping a term to a term of a different sort.
    #[error("trying to substitute term '{0}' with a term of a different sort: '{1}'")]
    DifferentSorts(Rc<Term>, Rc<Term>),
}

type SubstitutionResult<T> = Result<T, SubstitutionError>;

/// Represents a capture-avoiding substitution over terms.
///
/// A substitution is a mapping from variables to terms, that, when applied to a term, will replace
/// all instances of these variables to the terms that they map to. For example, applying the
/// substitution `{x -> (+ y 3)}` to the term `(and (> x 0) (= x z))` would result in the term
/// `(and (> (+ y 3) 0) (= (+ y 3) z))`.
///
/// Note that naively applying a substitution to a term that contains binders may result in what's
/// called a capture: when a variable that was supposed to be free is captured as the result of
/// applying the substitution to the binder term. Consider applying the substitution `{x -> y}` to
/// the term `(forall ((y Int)) (= x y))`. Doing so naively would result in the term
/// `(forall ((y Int)) (= y y))`, which has a different meaning than the original term, because the
/// `x` variable was captured by the binder when it was renamed. To prevent this, these
/// substitutions are also capture-avoiding. This is done by renaming the binder variable when
/// necessary before applying the substitution. In the earlier example, the resulting term would
/// actually be `(forall ((y' Int)) (= y y'))`.
#[derive(Debug, Clone)]
pub struct Substitution {
    /// The substitution's mappings.
    map: IndexMap<Rc<Term>, Rc<Term>>,

    /// The variables that should be renamed to preserve capture-avoidance, if they are bound by a
    /// binder term.
    should_be_renamed: Option<IndexSet<String>>,
    cache: IndexMap<Rc<Term>, Rc<Term>>,
}

impl Substitution {
    /// Constructs an empty substitution.
    pub fn empty() -> Self {
        Self {
            map: IndexMap::new(),
            should_be_renamed: None,
            cache: IndexMap::new(),
        }
    }

    /// Constructs a singleton substitution mapping `x` to `t`. This returns an error if the sorts
    /// of the given terms are not the same, or if `x` is not a variable term.
    pub fn single(pool: &mut dyn TermPool, x: Rc<Term>, t: Rc<Term>) -> SubstitutionResult<Self> {
        let mut this = Self::empty();
        this.insert(pool, x, t)?;
        Ok(this)
    }

    /// Constructs a new substitution from an arbitrary mapping of terms to other terms. This
    /// returns an error if any term in the left-hand side is not a variable, or if any term is
    /// mapped to a term of a different sort.
    pub fn new(
        pool: &mut dyn TermPool,
        map: IndexMap<Rc<Term>, Rc<Term>>,
    ) -> SubstitutionResult<Self> {
        for (k, v) in &map {
            if !k.is_var() && !k.is_sort_var() {
                return Err(SubstitutionError::NotAVariable(k.clone()));
            }
            if pool.sort(k) != pool.sort(v) {
                return Err(SubstitutionError::DifferentSorts(k.clone(), v.clone()));
            }
        }

        Ok(Self {
            map,
            should_be_renamed: None,
            cache: IndexMap::new(),
        })
    }

    /// Returns `true` if the substitution is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Extends the substitution by adding a new mapping from `x` to `t`. This returns an error if
    /// the sorts of the given terms are not the same, or if `x` is not a variable term.
    pub(crate) fn insert(
        &mut self,
        pool: &mut dyn TermPool,
        x: Rc<Term>,
        t: Rc<Term>,
    ) -> SubstitutionResult<()> {
        if !x.is_var() && !x.is_sort_var() {
            return Err(SubstitutionError::NotAVariable(x));
        }
        if pool.sort(&x) != pool.sort(&t) {
            return Err(SubstitutionError::DifferentSorts(x, t));
        }

        // Introducing new mappings may invalidate previously defined cache entries. In particular,
        // if a term contains `x` as a free variable, the result of applying the substitution to it
        // may be different after adding the `x -> t` mapping, so we remove these cache entries.
        self.cache.retain(|k, _| !pool.free_vars(k).contains(&x));

        if let Some(should_be_renamed) = &mut self.should_be_renamed {
            if x != t {
                let free_vars = pool
                    .free_vars(&t)
                    .into_iter()
                    .map(|v| v.as_var().unwrap().to_owned());
                should_be_renamed.extend(free_vars);
                if let Some(var) = x.as_var() {
                    should_be_renamed.insert(var.to_owned());
                }
            }
        }

        self.map.insert(x, t);
        Ok(())
    }

    /// Removes a mapping from the substitution.
    ///
    /// This will clear `self.should_be_renamed`, such that it might need to be recomputed later.
    /// Therefore, you should avoid using this method if possible.
    pub(super) fn remove(&mut self, x: &Rc<Term>) {
        let was_present = self.map.remove(x).is_some();
        if was_present {
            self.should_be_renamed = None;
        }
    }

    /// Computes which binder variables will need to be renamed, and stores the result in
    /// `self.should_be_renamed`.
    fn compute_should_be_renamed(&mut self, pool: &mut dyn TermPool) {
        if self.should_be_renamed.is_some() {
            return;
        }

        // To avoid captures when applying the substitution, we may need to rename some of the
        // variables that are bound in the term.
        //
        // For example, consider the substitution `{x -> y}`. If `x` and `y` are both variables,
        // when applying the substitution to `(forall ((y Int)) (= x y))`, we would need to rename
        // `y` to avoid a capture, because the substitution would change the semantics of the term.
        // The resulting term should then be `(forall ((y' Int)) (= y y'))`.
        //
        // More precisely, for a substitution `{x -> t}`, if a bound variable `y` satisfies one the
        // following conditions, it must be renamed:
        //
        // - `y` = `x`
        // - `y` appears in the free variables of `t`
        //
        // See https://en.wikipedia.org/wiki/Lambda_calculus#Capture-avoiding_substitutions for
        // more details.
        let mut should_be_renamed = IndexSet::new();
        for (x, t) in &self.map {
            if x == t {
                continue; // We ignore reflexive substitutions
            }
            let free_vars = pool
                .free_vars(t)
                .into_iter()
                .map(|v| v.as_var().unwrap().to_owned());
            should_be_renamed.extend(free_vars);
            if let Some(var) = x.as_var() {
                should_be_renamed.insert(var.to_owned());
            }
        }
        self.should_be_renamed = Some(should_be_renamed);
    }

    /// Applies the substitution to `term`, and returns the result as a new term.
    pub fn apply(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
        macro_rules! apply_to_sequence {
            ($sequence:expr) => {
                $sequence
                    .iter()
                    .map(|a| self.apply(pool, a))
                    .collect::<Vec<_>>()
            };
        }

        if let Some(t) = self.cache.get(term) {
            return t.clone();
        }
        if let Some(t) = self.map.get(term) {
            return t.clone();
        }

        let result = match term.as_ref() {
            Term::App(func, args) => {
                let new_args = apply_to_sequence!(args);
                let new_func = self.apply(pool, func);
                pool.add(Term::App(new_func, new_args))
            }
            Term::Op(op, args) => {
                let new_args = apply_to_sequence!(args);
                pool.add(Term::Op(*op, new_args))
            }
            Term::Binder(binder, binding_list, inner) => {
                self.apply_to_binder(pool, term, *binder, binding_list.as_ref(), inner)
            }
            Term::Let(binding_list, inner) => {
                let (new_bindings, mut renaming) =
                    self.rename_binding_list(pool, binding_list, true);
                let new_term = if renaming.is_empty() {
                    self.apply(pool, inner)
                } else {
                    // If there are variables that would be captured by the substitution, we need
                    // to rename them first
                    let renamed = renaming.apply(pool, inner);
                    self.apply(pool, &renamed)
                };
                pool.add(Term::Let(new_bindings, new_term))
            }
            Term::Const(_) | Term::Var(..) => term.clone(),
            Term::ParamOp { op, op_args, args } => {
                let new_args = apply_to_sequence!(args);
                pool.add(Term::ParamOp {
                    op: *op,
                    op_args: op_args.clone(),
                    args: new_args,
                })
            }
            Term::Sort(Sort::Atom(sort, args)) => {
                let new_args = apply_to_sequence!(args);
                pool.add(Term::Sort(Sort::Atom(sort.clone(), new_args)))
            }
            Term::Sort(Sort::Array(x, y)) => {
                let [x, y] = [x, y].map(|s| self.apply(pool, s));
                pool.add(Term::Sort(Sort::Array(x, y)))
            }
            Term::Sort(_) => term.clone(),
        };

        // Since frequently a term will have more than one identical subterms, we insert the
        // calculated substitution in the cache hash map so it may be reused later. This means we
        // don't re-visit already seen terms, so this method traverses the term as a DAG, not as a
        // tree
        self.cache.insert(term.clone(), result.clone());
        result
    }

    fn can_skip_instead_of_renaming(&self, binding_list: &[SortedVar]) -> bool {
        // Note: this method assumes that `binding_list` is a "sort" binding list. "Value" lists add
        // some complications that are currently not supported. For example, the variable in the
        // domain of the substitution might be used in the value of a binding in the binding list,
        // and the behavior of the substitution may change if this use is before or after the
        // variable is bound in the list.

        if self.map.len() != 1 {
            return false;
        }
        let x = self.map.iter().next().unwrap().0.as_var().unwrap();

        let mut should_be_renamed = binding_list
            .iter()
            .filter(|&var| self.should_be_renamed.as_ref().unwrap().contains(&var.0));

        // In order for skipping to be possible, there should be only one variable in the binding
        // list that would be renamed, and that variable must be the variable in the domain of the
        // substitution
        should_be_renamed.next().map(|(var, _)| var.as_ref()) == Some(x)
            && should_be_renamed.next().is_none()
    }

    /// Applies the substitution to a binder term, renaming any bound variables as needed.
    fn apply_to_binder(
        &mut self,
        pool: &mut dyn TermPool,
        original_term: &Rc<Term>,
        binder: Binder,
        binding_list: &[SortedVar],
        inner: &Rc<Term>,
    ) -> Rc<Term> {
        self.compute_should_be_renamed(pool);

        // In some situations, if the substitution has only one mapping (say, `x -> t`) we can skip
        // applying the substitution to a binder term altogether. This can happen if the variable
        // `x` appears in the binding list, while none of the free variables of `t` appear.
        // Normally, we would rename `x` to avoid shadowing before applying the substitution, but we
        // could instead remove the relevant mapping from the substitution, and add it back after
        // applying the substitution to the binder term. In this case, as there is only one mapping,
        // we can just skip the substitution entirely, which is way faster in some cases. In
        // particular, the skolemization rules require this optimization to have acceptable
        // performance.
        if self.can_skip_instead_of_renaming(binding_list) {
            return original_term.clone();
        }

        let (new_bindings, mut renaming) = self.rename_binding_list(pool, binding_list, false);
        let new_term = if renaming.is_empty() {
            self.apply(pool, inner)
        } else {
            // If there are variables that would be captured by the substitution, we need
            // to rename them first
            let renamed = renaming.apply(pool, inner);
            self.apply(pool, &renamed)
        };
        pool.add(Term::Binder(binder, new_bindings, new_term))
    }

    /// Creates a new substitution that renames all variables in the binding list that may be
    /// captured by this substitution to a new, arbitrary name. Returns that substitution, and the
    /// new binding list, with the bindings renamed. If no variable needs to be renamed, this just
    /// returns a clone of the binding list and an empty substitution. The name chosen when renaming
    /// a variable is the old name with `'` appended. If the binding list is a "value" list, like in
    /// a `let` or `lambda` term, `is_value_list` should be true.
    fn rename_binding_list(
        &mut self,
        pool: &mut dyn TermPool,
        binding_list: &[SortedVar],
        is_value_list: bool,
    ) -> (BindingList, Self) {
        let mut new_substitution = Self::empty();
        let mut new_vars = IndexSet::new();
        let new_binding_list = binding_list
            .iter()
            .map(|(var, value)| {
                // If the binding list is a "sort" binding list, then `value` will be the variable's
                // sort. Otherwise, we need to get the sort of `value`
                let sort = if is_value_list {
                    pool.sort(value)
                } else {
                    value.clone()
                };

                let mut changed = false;
                let mut new_var = var.clone();

                // We keep adding `'`s to the variable name as long as it is necessary
                loop {
                    if !new_vars.contains(&new_var)
                        && !self.should_be_renamed.as_ref().unwrap().contains(&new_var)
                    {
                        break;
                    }
                    new_var.push('\'');
                    changed = true;
                }

                if changed {
                    // If the variable was renamed, we have to add this renaming to the resulting
                    // substitution
                    let old = pool.add((var.clone(), sort.clone()).into());
                    let new = pool.add((new_var.clone(), sort).into());

                    // We can safely unwrap here because `old` and `new` are guaranteed to have the
                    // same sort
                    new_substitution.insert(pool, old, new).unwrap();
                    new_vars.insert(new_var.clone());
                }

                // If the binding list is a "value" list, we need to apply the current substitution
                // to each variable's value
                let new_value = if is_value_list {
                    new_substitution.apply(pool, value)
                } else {
                    value.clone()
                };
                (new_var, new_value)
            })
            .collect();
        (BindingList(new_binding_list), new_substitution)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::PrimitivePool, parser::*};

    fn run_test(definitions: &str, original: &str, x: &str, t: &str, result: &str) {
        let mut pool = PrimitivePool::new();
        let mut parser = Parser::new(&mut pool, Config::new(), definitions.as_bytes()).unwrap();
        parser.parse_problem().unwrap();

        let [original, x, t, result] = [original, x, t, result].map(|s| {
            parser.reset(s.as_bytes()).unwrap();
            parser.parse_term().unwrap()
        });

        let mut map = IndexMap::new();
        map.insert(x, t);

        let got = Substitution::new(&mut pool, map)
            .unwrap()
            .apply(&mut pool, &original);

        assert_eq!(&result, &got);
    }

    macro_rules! run_tests {
        (
            definitions = $defs:literal,
            $($original:literal [$x:tt -> $t:tt] => $result:literal,)*
        ) => {{
            let definitions = $defs;
            $(run_test(definitions, $original, stringify!($x), stringify!($t), $result);)*
        }};
    }

    #[test]
    fn test_substitutions() {
        run_tests! {
            definitions = "
                (declare-fun x () Int)
                (declare-fun y () Int)
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "x" [x -> x] => "x",
            "(+ 2 x)" [x -> y] => "(+ 2 y)",
            "(+ 2 x)" [x -> (+ 3 4 5)] => "(+ 2 (+ 3 4 5))",
            "(forall ((p Bool)) (and p q))" [q -> r] => "(forall ((p Bool)) (and p r))",

            // Simple renaming
            "(forall ((y Int)) (> y 0))" [x -> y] => "(forall ((y' Int)) (> y' 0))",

            // Renaming may be skipped
            "(forall ((x Int)) (> x 0))" [x -> y] => "(forall ((x Int)) (> x 0))",

            // Capture-avoidance
            "(forall ((y Int)) (> y x))" [x -> y] => "(forall ((y' Int)) (> y' y))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> y] =>
                "(forall ((x' Int) (y' Int)) (= x' y'))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> x] => "(forall ((x Int) (y Int)) (= x y))",
            "(forall ((y Int)) (> y x))" [x -> (+ y 0)] => "(forall ((y' Int)) (> y' (+ y 0)))",

            "(forall ((y Int) (y' Int)) (= y y'))" [x -> y] =>
                "(forall ((y' Int) (y'' Int)) (= y' y''))",
            "(forall ((y Int) (y' Int) (y'' Int)) (= y y' y''))" [x -> y] =>
                "(forall ((y' Int) (y'' Int) (y''' Int)) (= y' y'' y'''))",

            // The capture-avoidance may disambiguate repeated bindings
            "(forall ((y Int) (y' Int) (y' Int)) (= y y' y'))" [x -> y] =>
                "(forall ((y' Int) (y'' Int) (y''' Int)) (= y' y''' y'''))",

            // In theory, since x does not appear in this term, renaming y to y' is unnecessary
            "(forall ((y Int)) (> y 0))" [x -> y] => "(forall ((y' Int)) (> y' 0))",

            // Name collision with variables with different types
            "(forall ((y Bool)) (and y (> x 0)))" [x -> y] =>
                "(forall ((y' Bool)) (and y' (> y 0)))",

            // TODO: Add tests for `choice`, `let`, and `lambda` terms
        }
    }
}
