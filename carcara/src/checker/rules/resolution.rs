use super::{
    assert_clause_len, assert_eq, assert_is_bool_constant, assert_num_args, assert_num_premises,
    CheckerError, Premise, RuleArgs, RuleResult,
};
use crate::{ast::*, resolution::*};
use indexmap::IndexSet;

pub fn resolution(rule_args: RuleArgs) -> RuleResult {
    if !rule_args.args.is_empty() {
        // If the rule was given arguments, we redirect to the variant of "resolution" that takes
        // the pivots as arguments
        return resolution_with_args(rule_args);
    }
    let RuleArgs { conclusion, premises, pool, .. } = rule_args;

    // In some cases, this rule is used with a single premise `(not true)` to justify an empty
    // conclusion clause
    if conclusion.is_empty() && premises.len() == 1 {
        if let [t] = premises[0].clause {
            if match_term!((not true) = t).is_some() {
                return Ok(());
            }
        }
    }
    // Aside from this special case, all resolution steps must be between at least two clauses
    assert_num_premises(premises, 2..)?;

    let premise_clauses: Vec<_> = premises.iter().map(|p| p.clause).collect();

    greedy_resolution(conclusion, &premise_clauses, pool, false)
        .map(|_| ())
        .or_else(|greedy_error| {
            if rup_resolution(conclusion, premises) {
                Ok(())
            } else {
                // If RUP resolution also fails, we return the error originally returned by the greedy
                // algorithm
                Err(greedy_error.into())
            }
        })
}

fn rup_resolution(conclusion: &[Rc<Term>], premises: &[Premise]) -> bool {
    let mut clauses: Vec<IndexSet<(bool, &Rc<Term>)>> = premises
        .iter()
        .map(|p| {
            p.clause
                .iter()
                .map(Rc::remove_all_negations_with_polarity)
                .collect()
        })
        .collect();
    clauses.extend(conclusion.iter().map(|t| {
        let (p, t) = t.remove_all_negations_with_polarity();
        let mut clause = IndexSet::new();
        clause.insert((!p, t));
        clause
    }));

    loop {
        if clauses.is_empty() {
            return false;
        }
        let smallest = clauses.iter().min_by_key(|c| c.len()).unwrap();
        match smallest.len() {
            0 => return true,
            1 => {
                let literal = *smallest.iter().next().unwrap();
                let negated_literal = (!literal.0, literal.1);

                // Remove all clauses that contain the literal
                clauses.retain(|c| !c.contains(&literal));

                // Remove the negated literal from all clauses that contain it
                for c in &mut clauses {
                    c.remove(&negated_literal);
                }
            }
            _ => return false,
        }
    }
}

pub fn resolution_with_args(
    RuleArgs {
        conclusion, premises, args, pool, ..
    }: RuleArgs,
) -> RuleResult {
    let resolution_result = apply_generic_resolution::<IndexSet<_>>(premises, args, pool)?;

    let conclusion: IndexSet<_> = conclusion.iter().map(Rc::remove_all_negations).collect();

    if let Some(extra) = conclusion.difference(&resolution_result).next() {
        let extra = literal_to_term(pool, *extra);
        return Err(ResolutionError::ExtraTermInConclusion(extra).into());
    }
    if let Some(missing) = resolution_result.difference(&conclusion).next() {
        let missing = literal_to_term(pool, *missing);
        return Err(ResolutionError::MissingTermInConclusion(missing).into());
    }
    Ok(())
}

pub fn strict_resolution(
    RuleArgs {
        conclusion, premises, args, pool, ..
    }: RuleArgs,
) -> RuleResult {
    use std::cmp::Ordering;

    let resolution_result = apply_generic_resolution::<Vec<_>>(premises, args, pool)?;

    match conclusion.len().cmp(&resolution_result.len()) {
        Ordering::Less => {
            let missing = literal_to_term(pool, resolution_result[conclusion.len()]);
            Err(ResolutionError::MissingTermInConclusion(missing).into())
        }
        Ordering::Greater => {
            let extra = conclusion[resolution_result.len()].clone();
            Err(ResolutionError::ExtraTermInConclusion(extra).into())
        }
        Ordering::Equal => {
            for (t, u) in resolution_result.into_iter().zip(conclusion) {
                if t != u.remove_all_negations() {
                    assert_eq(&literal_to_term(pool, t), u)?;
                }
            }
            Ok(())
        }
    }
}

fn apply_generic_resolution<'a, C: ClauseCollection<'a>>(
    premises: &'a [Premise],
    args: &'a [Rc<Term>],
    pool: &mut dyn TermPool,
) -> Result<C, CheckerError> {
    assert_num_premises(premises, 2..)?;
    let num_steps = premises.len() - 1;
    assert_num_args(args, num_steps * 2)?;

    let args: Vec<_> = args
        .chunks(2)
        .map(|chunk| {
            let pivot = chunk[0].remove_all_negations();
            let polarity = chunk[1].clone();
            let polarity = if polarity.is_bool_true() {
                true
            } else if polarity.is_bool_false() {
                false
            } else {
                return Err(CheckerError::ExpectedAnyBoolConstant(polarity.clone()));
            };
            Ok((pivot, polarity))
        })
        .collect::<Result<_, _>>()?;

    let mut current = premises[0]
        .clause
        .iter()
        .map(Rc::remove_all_negations)
        .collect();

    for (premise, (pivot, polarity)) in premises[1..].iter().zip(args) {
        binary_resolution(pool, &mut current, premise.clause, pivot, polarity)?;
    }

    Ok(current)
}

fn binary_resolution<'a, C: ClauseCollection<'a>>(
    pool: &mut dyn TermPool,
    current: &mut C,
    next: &'a [Rc<Term>],
    pivot: Literal<'a>,
    is_pivot_in_current: bool,
) -> Result<(), ResolutionError> {
    let negated_pivot = (pivot.0 + 1, pivot.1);
    let (pivot_in_current, pivot_in_next) = if is_pivot_in_current {
        (pivot, negated_pivot)
    } else {
        (negated_pivot, pivot)
    };
    if !current.remove_term(&pivot_in_current) {
        let p = literal_to_term(pool, pivot_in_current);
        return Err(ResolutionError::PivotNotFound(p));
    }

    let mut found = false;
    for t in next {
        let t = t.remove_all_negations();
        if !found && t == pivot_in_next {
            found = true;
        } else {
            current.insert_term(t);
        }
    }
    if !found {
        let p = literal_to_term(pool, pivot_in_next);
        return Err(ResolutionError::PivotNotFound(p));
    }
    Ok(())
}

pub fn tautology(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;
    assert_is_bool_constant(&conclusion[0], true)?;

    let premise = premises[0].clause;
    let mut seen = IndexSet::with_capacity(premise.len());
    let with_negations_removed = premise.iter().map(Rc::remove_all_negations_with_polarity);
    for (polarity, term) in with_negations_removed {
        if seen.contains(&(!polarity, term)) {
            return Ok(());
        }
        seen.insert((polarity, term));
    }
    Err(ResolutionError::TautologyFailed.into())
}

pub fn contraction(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let premise_set: IndexSet<_> = premises[0].clause.iter().collect();
    let conclusion_set: IndexSet<_> = conclusion.iter().collect();
    if let Some(&t) = premise_set.difference(&conclusion_set).next() {
        Err(CheckerError::ContractionMissingTerm(t.clone()))
    } else if let Some(&t) = conclusion_set.difference(&premise_set).next() {
        Err(CheckerError::ContractionExtraTerm(t.clone()))
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn resolution() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
                (declare-fun t () Bool)
                (declare-fun u () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not p))
                (step t2 (cl p q) :rule hole)
                (step t3 (cl q) :rule resolution :premises (h1 t2))": true,

                "(step t1 (cl (not p) (not q) (not r)) :rule hole)
                (step t2 (cl p) :rule hole)
                (step t3 (cl q) :rule hole)
                (step t4 (cl r) :rule hole)
                (step t5 (cl) :rule resolution :premises (t1 t2 t3 t4))": true,
            }
            "Missing term in final clause" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule hole)
                (step t3 (cl q) :rule resolution :premises (h1 t2))": false,
            }
            "Term appears in final clause with wrong polarity" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule hole)
                (step t3 (cl (not q) r) :rule resolution :premises (h1 t2))": false,
            }
            "Duplicate term in final clause" {
                "(step t1 (cl q (not p)) :rule hole)
                (step t2 (cl p q r) :rule hole)
                (step t3 (cl q q r) :rule resolution :premises (t1 t2))": true,
            }
            "Terms with leading negations" {
                "(assume h1 (not p))
                (assume h2 (not (not p)))
                (assume h3 (not (not (not p))))
                (assume h4 (not (not (not (not p)))))
                (step t5 (cl) :rule resolution :premises (h1 h2))
                (step t6 (cl) :rule resolution :premises (h2 h3))
                (step t7 (cl (not p) (not (not (not p)))) :rule resolution :premises (h1 h3))
                (step t8 (cl (not p) (not (not (not (not p)))))
                    :rule resolution :premises (h1 h4))": true,
            }
            "Must use correct pivots" {
                "(step t1 (cl (not q) (not (not p)) (not p)) :rule hole)
                (step t2 (cl (not (not (not p))) p) :rule hole)
                (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))": true,

                "(step t1 (cl (not q) (not (not p)) (not p)) :rule hole)
                (step t2 (cl (not (not (not p))) p) :rule hole)
                (step t3 (cl (not q) (not (not (not p))) (not (not p)))
                    :rule resolution :premises (t1 t2))": true,

                "(step t1 (cl (not q) (not (not p)) (not p)) :rule hole)
                (step t2 (cl (not (not (not p))) p) :rule hole)
                (step t3 (cl (not q) p (not p) (not (not (not p))) (not (not p)))
                    :rule resolution :premises (t1 t2))": true,
            }
            "Weird behaviour where leading negations sometimes are added to conclusion" {
                "(assume h1 (not p))
                (step t2 (cl p q) :rule hole)
                (step t3 (cl (not (not q))) :rule resolution :premises (h1 t2))": true,
            }
            "Premise is \"(not true)\" and leads to empty conclusion clause" {
                "(step t1 (cl (not true)) :rule hole)
                (step t2 (cl) :rule th_resolution :premises (t1))": true,
            }
            "Repeated premises" {
                "(step t1 (cl (not r)) :rule hole)
                (step t2 (cl p q r s) :rule hole)
                (step t3 (cl p q s) :rule th_resolution :premises (t1 t2 t2))": true,
            }
            "Implicit elimination of \"(cl false)\"" {
                "(step t1 (cl p q false) :rule hole)
                (step t2 (cl (not p)) :rule hole)
                (step t3 (cl (not q)) :rule hole)
                (step t4 (cl) :rule resolution :premises (t1 t2 t3))": true,

                // This implicit elimination is allowed, but not required
                "(step t1 (cl p q false) :rule hole)
                (step t2 (cl (not p)) :rule hole)
                (step t3 (cl (not q)) :rule hole)
                (step t4 (cl false) :rule resolution :premises (t1 t2 t3))": true,
            }
            "Pivots given in arguments" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl (not q) s) :rule hole)
                (step t3 (cl p r s) :rule resolution :premises (t1 t2) :args (q true))": true,

                "(step t1 (cl p (not q) r) :rule hole)
                (step t2 (cl (not r) s q) :rule hole)
                (step t3 (cl p r (not r) s)
                    :rule resolution :premises (t1 t2) :args (q false))": true,

                "(step t1 (cl p q) :rule hole)
                (step t2 (cl (not q) (not r)) :rule hole)
                (step t3 (cl (not s) (not (not r)) t) :rule hole)
                (step t4 (cl s (not t) u) :rule hole)
                (step t5 (cl p t (not t) u)
                    :rule resolution
                    :premises (t1 t2 t3 t4)
                    :args (q true (not r) true s false))": true,
            }
            "Only one pivot eliminated per clause" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl (not q) (not r)) :rule hole)
                (step t3 (cl p) :rule resolution :premises (t1 t2))": false,
            }
            "`th_resolution` may receive premises in wrong order" {
                "(step t1 (cl (not p) (not q) (not r)) :rule hole)
                (step t2 (cl p) :rule hole)
                (step t3 (cl q) :rule hole)
                (step t4 (cl r) :rule hole)
                (step t5 (cl) :rule th_resolution :premises (t4 t3 t2 t1))": true,

                "(step t1 (cl (not p) (not q) (not r)) :rule hole)
                (step t2 (cl p) :rule hole)
                (step t3 (cl q) :rule hole)
                (step t4 (cl r) :rule hole)
                (step t5 (cl) :rule th_resolution :premises (t1 t2 t3 t4))": true,
            }
            "Number of premises must be at least two" {
                "(step t1 (cl) :rule resolution)": false,

                "(assume h1 true)
                (step t2 (cl true) :rule resolution :premises (h1))": false,
            }
        }
    }

    #[test]
    fn strict_resolution() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
                (declare-fun t () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl s (not r) t) :rule hole)
                (step t3 (cl p q s t)
                    :rule strict_resolution
                    :premises (t1 t2)
                    :args (r true))": true,
            }
            "No implicit reordering" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl s (not r) t) :rule hole)
                (step t3 (cl t s q p)
                    :rule strict_resolution
                    :premises (t1 t2)
                    :args (r true))": false,

                "(step t1 (cl p q) :rule hole)
                (step t2 (cl r (not q) s) :rule hole)
                (step t3 (cl (not r) t) :rule hole)
                (step t4 (cl p t s)
                    :rule strict_resolution
                    :premises (t1 t2 t3)
                    :args (q true r true))": false,
            }
            "No implicit removal of duplicates" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl (not q) s) :rule hole)
                (step t3 (cl (not r) s) :rule hole)
                (step t4 (cl p s s)
                    :rule strict_resolution
                    :premises (t1 t2 t3)
                    :args (q true r true))": true,

                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl (not q) s) :rule hole)
                (step t3 (cl (not r) s) :rule hole)
                (step t4 (cl p s)
                    :rule strict_resolution
                    :premises (t1 t2 t3)
                    :args (q true r true))": false,

                // Duplicates also can't be implicitly introduced
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl s (not r) t) :rule hole)
                (step t3 (cl p q s t s)
                    :rule strict_resolution
                    :premises (t1 t2)
                    :args (r true))": false,
            }
        }
    }

    #[test]
    fn tautology() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not p) p) :rule hole)
                (step t2 (cl true) :rule tautology :premises (t1))": true,

                "(step t1 (cl p q (not q) r s) :rule hole)
                (step t2 (cl true) :rule tautology :premises (t1))": true,

                "(step t1 (cl p (not (not s)) q r (not (not (not s)))) :rule hole)
                (step t2 (cl true) :rule tautology  :premises (t1))": true,
            }
            "Conclusion is not \"true\"" {
                "(step t1 (cl p q (not q) r s) :rule hole)
                (step t2 (cl false) :rule tautology :premises (t1))": false,

                "(step t1 (cl p q (not q) r s) :rule hole)
                (step t2 (cl) :rule tautology :premises (t1))": false,
            }
            "Premise is not a tautology" {
                "(step t1 (cl p) :rule hole)
                (step t2 (cl true) :rule tautology :premises (t1))": false,

                "(step t1 (cl p (not (not s)) q r s) :rule hole)
                (step t2 (cl true) :rule tautology :premises (t1))": false,
            }
        }
    }

    #[test]
    fn contraction() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl p q q r s s) :rule hole)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

                "(step t1 (cl p p p q q r s s s) :rule hole)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

                "(step t1 (cl p q r s) :rule hole)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,
            }
            "Number of premises != 1" {
                "(step t1 (cl p q) :rule contraction)": false,

                "(assume h1 q)
                (assume h2 p)
                (step t3 (cl p q) :rule contraction :premises (h1 h2))": false,
            }
            "Premise is not a \"step\" command" {
                "(assume h1 q)
                (step t2 (cl q) :rule contraction :premises (h1))": true,
            }
            "Not all terms removed" {
                "(step t1 (cl p p q q) :rule hole)
                (step t2 (cl p p q) :rule contraction :premises (t1))": true,

                "(step t1 (cl q p p q q) :rule hole)
                (step t2 (cl q p q) :rule contraction :premises (t1))": true,
            }
            "Terms are not in correct order" {
                "(step t1 (cl p q q r) :rule hole)
                (step t2 (cl p r q) :rule contraction :premises (t1))": true,
            }
            "Conclusion is missing terms" {
                "(step t1 (cl p q q r) :rule hole)
                (step t2 (cl p r) :rule contraction :premises (t1))": false,

                "(step t1 (cl p p q r) :rule hole)
                (step t2 (cl p q) :rule contraction :premises (t1))": false,
            }
            "Conclusion has extra term at the end" {
                "(step t1 (cl p p q) :rule hole)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": false,
            }
        }
    }
}
