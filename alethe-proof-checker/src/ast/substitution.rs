use super::{BindingList, Rc, SortedVar, Term, TermPool};
use ahash::{AHashMap, AHashSet};
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
pub enum SubstitutionError {
    #[error("trying to substitute term '{0}' with a term of different sort: '{1}'")]
    DifferentSorts(Rc<Term>, Rc<Term>),
}

type SubstitutionResult<T> = Result<T, SubstitutionError>;

pub struct Substitution {
    pub(crate) map: AHashMap<Rc<Term>, Rc<Term>>,
    // Variables that should be renamed to preserve capture-avoidance if they are bound by a binder
    // term
    should_be_renamed: AHashSet<String>,
    cache: AHashMap<Rc<Term>, Rc<Term>>,
}

impl Substitution {
    pub fn empty() -> Self {
        Self {
            map: AHashMap::new(),
            should_be_renamed: AHashSet::new(),
            cache: AHashMap::new(),
        }
    }

    pub fn single(pool: &mut TermPool, x: Rc<Term>, t: Rc<Term>) -> SubstitutionResult<Self> {
        let mut this = Self::empty();
        this.insert(pool, x, t)?;
        Ok(this)
    }

    pub fn new(pool: &mut TermPool, map: AHashMap<Rc<Term>, Rc<Term>>) -> SubstitutionResult<Self> {
        for (k, v) in map.iter() {
            if pool.sort(k) != pool.sort(v) {
                return Err(SubstitutionError::DifferentSorts(k.clone(), v.clone()));
            }
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
        let mut should_be_renamed = AHashSet::new();
        for (x, t) in map.iter() {
            if x == t {
                continue; // We ignore reflexive substitutions
            }
            should_be_renamed.extend(pool.free_vars(t).iter().cloned());
            if let Some(x) = x.as_var() {
                should_be_renamed.insert(x.to_owned());
            }
        }

        Ok(Self {
            map,
            should_be_renamed,
            cache: AHashMap::new(),
        })
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Extends the substitution by adding a new mapping from `x` to `t`.
    pub(crate) fn insert(
        &mut self,
        pool: &mut TermPool,
        x: Rc<Term>,
        t: Rc<Term>,
    ) -> SubstitutionResult<()> {
        if pool.sort(&x) != pool.sort(&t) {
            return Err(SubstitutionError::DifferentSorts(x, t));
        }

        if x != t {
            self.should_be_renamed
                .extend(pool.free_vars(&t).iter().cloned());
            if let Some(x) = x.as_var() {
                self.should_be_renamed.insert(x.to_owned());
            }
        }

        self.map.insert(x, t);
        Ok(())
    }

    pub fn apply(&mut self, pool: &mut TermPool, term: &Rc<Term>) -> Rc<Term> {
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
                pool.add_term(Term::App(new_func, new_args))
            }
            Term::Op(op, args) => {
                let new_args = apply_to_sequence!(args);
                pool.add_term(Term::Op(*op, new_args))
            }
            Term::Quant(q, b, t) => {
                let (new_bindings, new_term) = self.apply_to_binder(pool, b.as_ref(), t, false);
                pool.add_term(Term::Quant(*q, new_bindings, new_term))
            }
            Term::Choice(var, t) => {
                let (mut new_bindings, new_term) =
                    self.apply_to_binder(pool, std::slice::from_ref(var), t, false);
                let new_var = new_bindings.0.pop().unwrap();
                pool.add_term(Term::Choice(new_var, new_term))
            }
            Term::Let(b, t) => {
                let (new_bindings, new_term) = self.apply_to_binder(pool, b.as_ref(), t, true);
                pool.add_term(Term::Let(new_bindings, new_term))
            }
            Term::Lambda(b, t) => {
                let (new_bindings, new_term) = self.apply_to_binder(pool, b.as_ref(), t, true);
                pool.add_term(Term::Lambda(new_bindings, new_term))
            }
            Term::Terminal(_) | Term::Sort(_) => term.clone(),
        };

        // Since frequently a term will have more than one identical subterms, we insert the
        // calculated substitution in the cache hash map so it may be reused later. This means we
        // don't re-visit already seen terms, so this method traverses the term as a DAG, not as a
        // tree
        self.cache.insert(term.clone(), result.clone());
        result
    }

    fn apply_to_binder(
        &mut self,
        pool: &mut TermPool,
        binding_list: &[SortedVar],
        inner: &Rc<Term>,
        is_value_list: bool,
    ) -> (BindingList, Rc<Term>) {
        let (new_bindings, mut renaming) =
            self.rename_binding_list(pool, binding_list, is_value_list);
        let new_term = if renaming.is_empty() {
            self.apply(pool, inner)
        } else {
            // If there are variables that would be captured by the substitution, we need
            // to rename them first
            let renamed = renaming.apply(pool, inner);
            self.apply(pool, &renamed)
        };
        (new_bindings, new_term)
    }

    /// Creates a new substitution that renames all variables in the binding list that may be
    /// captured by this substitution to a new, arbitrary name. Returns that substitution, and the
    /// new binding list, with the bindings renamed. If no variable needs to be renamed, this just
    /// returns a clone of the binding list and an empty substitution. The name chosen when renaming
    /// a variable is the old name with '@' appended. If the binding list is a "value" list, like in
    /// a `let` or `lambda` term, `is_value_list` should be true.
    fn rename_binding_list(
        &mut self,
        pool: &mut TermPool,
        binding_list: &[SortedVar],
        is_value_list: bool,
    ) -> (BindingList, Self) {
        let mut new_substitution = Self::empty();
        let mut new_vars = AHashSet::new();
        let new_binding_list = binding_list
            .iter()
            .map(|(var, value)| {
                // If the binding list is a "sort" binding list, then `value` will be the variable's
                // sort. Otherwise, we need to get the sort of `value`
                let sort = if is_value_list {
                    pool.add_term(Term::Sort(pool.sort(value).clone()))
                } else {
                    value.clone()
                };

                let mut changed = false;
                let mut new_var = var.clone();

                // We keep adding `@`s to the variable name as long as it is necessary
                while self.should_be_renamed.contains(&new_var) || new_vars.contains(&new_var) {
                    new_var.push('@');
                    changed = true;
                }
                if changed {
                    // If the variable was renamed, we have to add this renaming to the resulting
                    // substitution
                    let old = pool.add_term((var.clone(), sort.clone()).into());
                    let new = pool.add_term((new_var.clone(), sort).into());

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
    use crate::parser::*;

    fn run_test(definitions: &str, original: &str, x: &str, t: &str, result: &str) {
        let mut parser = Parser::new(definitions.as_bytes(), true).unwrap();
        parser.parse_problem().unwrap();

        let [original, x, t, result] = [original, x, t, result].map(|s| {
            parser.reset(s.as_bytes()).unwrap();
            parser.parse_term().unwrap()
        });

        let mut map = AHashMap::new();
        map.insert(x, t);

        let mut pool = parser.term_pool();
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
            "(forall ((x Int)) (> x 0))" [x -> y] => "(forall ((x@ Int)) (> x@ 0))",

            // Capture-avoidance
            "(forall ((y Int)) (> y x))" [x -> y] => "(forall ((y@ Int)) (> y@ y))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> y] =>
                "(forall ((x@ Int) (y@ Int)) (= x@ y@))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> x] => "(forall ((x Int) (y Int)) (= x y))",
            "(forall ((y Int)) (> y x))" [x -> (+ y 0)] => "(forall ((y@ Int)) (> y@ (+ y 0)))",
            "(forall ((x Int) (x@ Int)) (= x x@))" [x -> y] =>
                "(forall ((x@ Int) (x@@ Int)) (= x@ x@@))",
            "(forall ((x Int) (x@ Int) (x@@ Int)) (= x x@ x@@))" [x -> y] =>
                "(forall ((x@ Int) (x@@ Int) (x@@@ Int)) (= x@ x@@ x@@@))",

            // The capture-avoidance may disambiguate repeated bindings
            "(forall ((x Int) (x@ Int) (x@ Int)) (= x x@ x@))" [x -> y] =>
                "(forall ((x@ Int) (x@@ Int) (x@@@ Int)) (= x@ x@@@ x@@@))",

            // In theory, since x does not appear in this term, renaming y to y@ is unnecessary
            "(forall ((y Int)) (> y 0))" [x -> y] => "(forall ((y@ Int)) (> y@ 0))",

            // TODO: Add tests for `choice`, `let`, and `lambda` terms
        }
    }
}
