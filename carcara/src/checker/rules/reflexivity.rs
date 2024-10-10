use super::{assert_clause_len, assert_eq, CheckerError, RuleArgs, RuleResult};
use crate::ast::*;

pub fn eq_reflexive(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (a, b) = match_term_err!((= a b) = &conclusion[0])?;
    assert_eq(a, b)
}

pub fn refl(
    RuleArgs {
        conclusion,
        pool,
        context,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    // If the two terms are directly identical, we don't need to do any more work. We make sure to
    // do this check before we try to get the context substitution, because `refl` can be used
    // outside of any subproof
    if alpha_equiv(left, right, polyeq_time) {
        return Ok(());
    }

    if context.is_empty() {
        return Err(CheckerError::ReflexivityFailed(left.clone(), right.clone()));
    }

    // In some cases, the substitution is only applied to the left or the right term, and in some
    // cases it is applied to both. To cover all cases, we must check all three possibilities. We
    // don't compute the new left and right terms until they are needed, to avoid doing unnecessary
    // work
    let new_left = context.apply(pool, left);
    let result = alpha_equiv(&new_left, right, polyeq_time) || {
        let new_right = context.apply(pool, right);
        alpha_equiv(left, &new_right, polyeq_time)
            || alpha_equiv(&new_left, &new_right, polyeq_time)
    };
    rassert!(
        result,
        CheckerError::ReflexivityFailed(left.clone(), right.clone()),
    );
    Ok(())
}

pub fn strict_refl(RuleArgs { conclusion, pool, context, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    if left == right {
        return Ok(());
    }
    if context.is_empty() {
        return Err(CheckerError::ReflexivityFailed(left.clone(), right.clone()));
    }

    // This follows the same logic as the `refl` function, but without using alpha equivalence
    let new_left = context.apply(pool, left);
    let result = new_left == *right || {
        let new_right = context.apply(pool, right);
        *left == new_right || new_left == new_right
    };
    rassert!(
        result,
        CheckerError::ReflexivityFailed(left.clone(), right.clone()),
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn eq_reflexive() {
        test_cases! {
            definitions = "
                (declare-fun a () Int)
                (declare-fun b () Int)
                (declare-fun f (Int Int) Int)
            ",
            "Simple working examples" {
                "(step t1 (cl (= a a)) :rule eq_reflexive)": true,
                "(step t1 (cl (= false false)) :rule eq_reflexive)": true,
                "(step t1 (cl (= (f a b) (f a b))) :rule eq_reflexive)": true,
                "(step t1 (cl (= (+ b a) (+ b a))) :rule eq_reflexive)": true,
            }
            "Number of terms in clause != 1" {
                "(step t1 (cl) :rule eq_reflexive)": false,
                "(step t1 (cl (= a a) (= b b)) :rule eq_reflexive)": false,
            }
            "Term is not an equality" {
                "(step t1 (cl (not (= b b))) :rule eq_reflexive)": false,
                "(step t1 (cl (and (= a a) (= b b))) :rule eq_reflexive)": false,
            }
            "Terms in equality aren't equal" {
                "(step t1 (cl (= a b)) :rule eq_reflexive)": false,
                "(step t1 (cl (= (f a b) (f b a))) :rule eq_reflexive)": false,
                "(step t1 (cl (= (+ a b) (+ b a))) :rule eq_reflexive)": false,
            }
        }
    }

    #[test]
    fn refl() {
        test_cases! {
            definitions = "
                (declare-fun f (Real) Real)
                (declare-fun g (Real) Real)
                (declare-fun z () Real)
            ",
            "Simple working examples" {
                "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
                (step t1.t1 (cl (= x y)) :rule refl)
                (step t1 (cl) :rule hole)": true,

                "(anchor :step t1)
                (step t1.t1 (cl (= z z)) :rule refl)
                (step t1 (cl) :rule hole)": true,

            }
            "Multiple substitutions in sequence" {
                "(anchor :step t1 :args ((z Real) (:= (y Real) z) (:= (x Real) y)))
                (step t1.t1 (cl (= x z)) :rule refl)
                (step t1 (cl) :rule hole)": true,
            }
            "Nested subproofs" {
                // Since an inner subproof cannot end an outer subproof, we need to have a dummy
                // step to the end the outer subproofs in these examples

                // This step is valid because the outer context transforms the `y` in the `(:= x y)`
                // mapping, such that the context becomes `(:= x z)`
                "(anchor :step t1 :args ((z Real) (:= (y Real) z)))
                (anchor :step t1.t1 :args ((:= (x Real) y)))
                (step t1.t1.t1 (cl (= x z)) :rule refl)
                (step t1.t1 (cl) :rule hole)
                (step t1 (cl) :rule hole)": true,

                // This should fail because the semantics of `refl` are such that the substitution
                // is simultaneous, and not until a fixed point
                "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
                (anchor :step t1.t1 :args ((z Real) (:= (y Real) z)))
                (step t1.t1.t1 (cl (= x z)) :rule refl)
                (step t1.t1 (cl) :rule hole)
                (step t1 (cl) :rule hole)": false,
            }
            "Terms aren't equal after applying context substitution" {
                "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
                (step t1.t1 (cl (= x z)) :rule refl)
                (step t1 (cl) :rule hole)": false,
            }
            "Name collision with variables of different types" {
                "(anchor :step t1 :args ((y Int) (:= (x Int) y)))
                (step t1.t1 (cl (=
                    (forall ((y Bool)) (and y (> x 0)))
                    (forall ((z Bool)) (and z (> y 0)))
                )) :rule refl)
                (step t1 (cl) :rule hole)": true,
            }
        }
    }
}
