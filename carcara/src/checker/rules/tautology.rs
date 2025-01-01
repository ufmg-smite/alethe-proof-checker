use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, assert_polyeq,
    get_premise_term, CheckerError, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::rules::assert_operation_len};

pub fn r#true(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    if !conclusion[0].is_bool_true() {
        return Err(CheckerError::ExpectedBoolConstant(
            true,
            conclusion[0].clone(),
        ));
    }
    Ok(())
}

pub fn r#false(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let t = conclusion[0].remove_negation_err()?;
    if !t.is_bool_false() {
        return Err(CheckerError::ExpectedBoolConstant(false, t.clone()));
    }
    Ok(())
}

pub fn not_not(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;

    let p = match_term_err!((not (not (not p))) = &conclusion[0])?;
    assert_eq(p, &conclusion[1])
}

pub fn and_pos(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    assert_num_args(args, 1)?;

    let and_contents = match_term_err!((not (and ...)) = &conclusion[0])?;
    let i = args[0].as_usize_err()?;

    if i >= and_contents.len() {
        return Err(CheckerError::NoIthChildInTerm(i, conclusion[0].clone()));
    }

    assert_eq(&conclusion[1], &and_contents[i])
}

pub fn and_neg(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2..)?;

    let and_contents = match_term_err!((and ...) = &conclusion[0])?;
    assert_operation_len(Operator::And, and_contents, conclusion.len() - 1)?;

    for (t, u) in and_contents.iter().zip(&conclusion[1..]) {
        let u = u.remove_negation_err()?;
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn or_pos(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2..)?;

    let or_contents = match_term_err!((not (or ...)) = &conclusion[0])?;
    assert_operation_len(Operator::Or, or_contents, conclusion.len() - 1)?;

    for (t, u) in or_contents.iter().zip(&conclusion[1..]) {
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn or_neg(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    assert_num_args(args, 1)?;

    let or_contents = match_term_err!((or ...) = &conclusion[0])?;
    let other = conclusion[1].remove_negation_err()?;
    let i = args[0].as_usize_err()?;

    if i >= or_contents.len() {
        return Err(CheckerError::NoIthChildInTerm(i, conclusion[0].clone()));
    }

    assert_eq(other, &or_contents[i])
}

pub fn xor_pos1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (xor phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn xor_pos2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (xor phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn xor_neg1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn xor_neg2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn implies_pos(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (=> phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn implies_neg1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    let (phi_1, _) = match_term_err!((=> phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])
}

pub fn implies_neg2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    let (_, phi_2) = match_term_err!((=> phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn equiv_pos1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (= phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn equiv_pos2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((not (= phi_1 phi_2)) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn equiv_neg1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn equiv_neg2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn ite_pos1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, _, phi_3) = match_term_err!((not (ite phi_1 phi_2 phi_3)) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_3, &conclusion[2])
}

pub fn ite_pos2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2, _) = match_term_err!((not (ite phi_1 phi_2 phi_3)) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[2])
}

pub fn ite_neg1(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, _, phi_3) = match_term_err!((ite phi_1 phi_2 phi_3) = &conclusion[0])?;
    assert_eq(phi_1, &conclusion[1])?;
    assert_eq(phi_3, conclusion[2].remove_negation_err()?)
}

pub fn ite_neg2(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3)?;
    let (phi_1, phi_2, _) = match_term_err!((ite phi_1 phi_2 phi_3) = &conclusion[0])?;
    assert_eq(phi_1, conclusion[1].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[2].remove_negation_err()?)
}

pub fn equiv1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = premise_term)?;
    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn equiv2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = premise_term)?;
    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn not_equiv1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((not (= phi_1 phi_2)) = premise_term)?;
    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn not_equiv2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((not (= phi_1 phi_2)) = premise_term)?;
    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn ite1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, _, phi_3) = match_term_err!((ite phi_1 phi_2 phi_3) = premise_term)?;
    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_3, &conclusion[1])
}

pub fn ite2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2, _) = match_term_err!((ite phi_1 phi_2 phi_3) = premise_term)?;
    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn not_ite1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, _, phi_3) = match_term_err!((not (ite phi_1 phi_2 phi_3)) = premise_term)?;
    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_3, conclusion[1].remove_negation_err()?)
}

pub fn not_ite2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;
    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2, _) = match_term_err!((not (ite phi_1 phi_2 phi_3)) = premise_term)?;
    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn ite_intro(RuleArgs { conclusion, polyeq_time, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (root_term, right_side) = match_term_err!((= t u) = &conclusion[0])?;

    // In some cases, no `ite` subterm is extracted from `t` (even if `t` has `ite` subterms), so
    // the conjunction in the right side of the equality has only one term: `t` itself, modulo
    // reordering of equalities. One example where this happens is the test file
    // SH_problems_all_filtered/isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_15_09_29_511_18566192.smt_in.proof
    // Step `t7` in that proof is:
    // ```
    //     (step t7 (cl (=
    //         (= (times$ c$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)))
    //            (times$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)) c$))
    //         (= (times$ c$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)))
    //            (times$ (ite (< (g$ n$) 0.0) (- (g$ n$)) (g$ n$)) c$))
    //     )) :rule ite_intro)
    // ```
    // For cases like this, we first check if `t` equals the right side term modulo reordering of
    // equalities. If not, we unwrap the conjunction and continue checking the rule normally.
    if polyeq(root_term, right_side, polyeq_time) {
        return Ok(());
    }
    let us = match_term_err!((and ...) = right_side)?;

    // `us` must be a conjunction where the first term is the root term
    assert_polyeq(&us[0], root_term, polyeq_time)?;

    // The remaining terms in `us` should be of the correct form
    for u_i in &us[1..] {
        let (cond, (a, b), (c, d)) = match_term_err!((ite cond (= a b) (= c d)) = u_i)?;

        let mut is_valid = |r_1, s_1, r_2, s_2| {
            // s_1 == s_2 == (ite cond r_1 r_2)
            if polyeq(s_1, s_2, polyeq_time) {
                if let Some((a, b, c)) = match_term!((ite a b c) = s_1) {
                    return polyeq(a, cond, polyeq_time)
                        && polyeq(b, r_1, polyeq_time)
                        && polyeq(c, r_2, polyeq_time);
                }
            }
            false
        };
        // Since the (= r_1 s_1) and (= r_2 s_2) equalities may be flipped, we have to check all
        // four possibilities: neither are flipped, either one is flipped, or both are flipped
        let is_valid = is_valid(a, b, c, d)
            || is_valid(b, a, c, d)
            || is_valid(a, b, d, c)
            || is_valid(b, a, d, c);

        if !is_valid {
            return Err(CheckerError::IsNotValidIteIntro(u_i.clone()));
        }
    }
    Ok(())
}

pub fn connective_def(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (first, second) = match_term_err!((= f s) = &conclusion[0])?;

    if let Some((phi_1, phi_2)) = match_term!((xor phi_1 phi_2) = first) {
        // phi_1 xor phi_2 <-> (¬phi_1 ^ phi_2) v (phi_1 ^ ¬phi_2)
        let ((a, b), (c, d)) = match_term_err!((or (and (not a) b) (and c (not d))) = second)?;
        assert_eq(a, phi_1)?;
        assert_eq(b, phi_2)?;
        assert_eq(c, phi_1)?;
        assert_eq(d, phi_2)
    } else if let Some((phi_1, phi_2)) = match_term!((= phi_1 phi_2) = first) {
        // (phi_1 <-> phi_2) <-> (phi_1 -> phi_2) ^ (phi_2 -> phi_1)
        let ((a, b), (c, d)) = match_term_err!((and (=> a b) (=> c d)) = second)?;
        assert_eq(a, phi_1)?;
        assert_eq(b, phi_2)?;
        assert_eq(c, phi_2)?;
        assert_eq(d, phi_1)
    } else if let Some((phi_1, phi_2, phi_3)) = match_term!((ite phi_1 phi_2 phi_3) = first) {
        // ite phi_1 phi_2 phi_3 <-> (phi_1 -> phi_2) ^ (¬phi_1 -> phi_3)
        let ((a, b), (c, d)) = match_term_err!((and (=> a b) (=> (not c) d)) = second)?;
        assert_eq(a, phi_1)?;
        assert_eq(b, phi_2)?;
        assert_eq(c, phi_1)?;
        assert_eq(d, phi_3)
    } else if let Some((first_bindings, first_inner)) = match_term!((forall ... f) = first) {
        let (second_bindings, second_inner) = match_term_err!((not (exists ... (not s))) = second)?;
        assert_eq(first_inner, second_inner)?;
        assert_eq(first_bindings, second_bindings)
    } else {
        Err(CheckerError::TermIsNotConnective(first.clone()))
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn r#true() {
        test_cases! {
            definitions = "",
            "Simple working examples" {
                "(step t1 (cl true) :rule true)": true,
            }
            "Failing examples" {
                "(step t1 (cl false true) :rule true)": false,
                "(step t1 (cl (not true)) :rule true)": false,
                "(step t1 (cl (not false)) :rule true)": false,
                "(step t1 (cl (= 0 0)) :rule true)": false,
            }
        }
    }

    #[test]
    fn r#false() {
        test_cases! {
            definitions = "",
            "Simple working examples" {
                "(step t1 (cl (not false)) :rule false)": true,
            }
            "Failing examples" {
                "(step t1 (cl false true) :rule false)": false,
                "(step t1 (cl (not true)) :rule false)": false,
                "(step t1 (cl true) :rule false)": false,
                "(step t1 (cl (= 0 0)) :rule false)": false,
            }
        }
    }

    #[test]
    fn not_not() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (not (not p))) p) :rule not_not)": true,
                "(step t1 (cl (not (not (not (not q)))) (not q)) :rule not_not)": true,
            }
            "Number of terms in clause != 2" {
                "(step t1 (cl (not (not (not p)))) :rule not_not)": false,
                "(step t1 (cl (not (not (not p))) p q) :rule not_not)": false,
            }
            "First term in clause is not of the correct form" {
                "(step t1 (cl (not (not p)) (not p)) :rule not_not)": false,
                "(step t1 (cl p (not p)) :rule not_not)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (not (not p))) (not p)) :rule not_not)": false,
                "(step t1 (cl (not (not (not p))) q) :rule not_not)": false,
            }
        }
    }

    #[test]
    fn and_pos() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (and p q r)) r) :rule and_pos :args (2))": true,
                "(step t1 (cl (not (and (or (not r) p) q)) (or (not r) p)) :rule and_pos :args (0))": true,
            }
            "First term in clause is not of the correct form" {
                "(step t1 (cl (and p q r) r) :rule and_pos)": false,
                "(step t1 (cl (not (or p q r)) r) :rule and_pos)": false,
            }
            "Second term is not in \"and\" term" {
                "(step t1 (cl (not (and p q r)) s) :rule and_pos)": false,
                "(step t1 (cl (not (and p (not q) r)) q) :rule and_pos)": false,
            }
        }
    }

    #[test]
    fn and_neg() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (and p q) (not p) (not q)) :rule and_neg)": true,
                "(step t1 (cl (and p q r s) (not p) (not q) (not r) (not s)) :rule and_neg)": true,
            }
            "First term in clause is not of the correct form" {
                "(step t1 (cl (or p q r) (not p) (not q) (not r)) :rule and_neg)": false,
            }
            "Remaining terms in clause are not of the correct form" {
                "(step t1 (cl (and p q) p (not q)) :rule and_neg)": false,
            }
            "Number of remaining terms is incorrect" {
                "(step t1 (cl (and p q r) (not p) (not q) (not r) (not s)) :rule and_neg)": false,
                "(step t1 (cl (and p q r) (not p) (not q)) :rule and_neg)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (and p q r) (not p) (not q) (not s)) :rule and_neg)": false,
                "(step t1 (cl (and p q r s) (not p) (not r) (not q) (not s)) :rule and_neg)": false,
            }
        }
    }

    #[test]
    fn or_pos() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (or p q)) p q) :rule or_pos)": true,
                "(step t1 (cl (not (or p q r s)) p q r s) :rule or_pos)": true,
            }
            "First term in clause is not of the correct form" {
                "(step t1 (cl (or p q r) p q r) :rule or_pos)": false,
                "(step t1 (cl (not (and p q r)) p q r) :rule or_pos)": false,
            }
            "Number of remaining terms is incorrect" {
                "(step t1 (cl (not (or p q r)) p q) :rule or_pos)": false,
                "(step t1 (cl (not (or p q r)) p q r s) :rule or_pos)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (or p q r)) p q s) :rule or_pos)": false,
                "(step t1 (cl (not (or p q r s)) p r q s) :rule or_pos)": false,
            }
        }
    }

    #[test]
    fn or_neg() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (or p q r) (not r)) :rule or_neg :args (2))": true,
            }
            "First term in clause is not of the correct form" {
                "(step t1 (cl (and p q r) (not r)) :rule or_neg)": false,
                "(step t1 (cl (not (or p q r)) (not r)) :rule or_neg)": false,
            }
            "Second term is not in \"or\" term" {
                "(step t1 (cl (or p q r) (not s)) :rule or_neg)": false,
                "(step t1 (cl (or p (not q) r) (not q)) :rule or_neg)": false,

            }
        }
    }

    #[test]
    fn xor_pos1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (xor p q)) p q) :rule xor_pos1)": true,
                "(step t1 (cl (not (xor (not p) q)) (not p) q) :rule xor_pos1)": true,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (xor p q) p q) :rule xor_pos1)": false,
                "(step t1 (cl (and p q) p q) :rule xor_pos1)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (xor p q)) q p) :rule xor_pos1)": false,
                "(step t1 (cl (not (xor (not p) q)) p (not q)) :rule xor_pos1)": false,
            }
        }
    }

    #[test]
    fn xor_pos2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (xor p q)) (not p) (not q)) :rule xor_pos2)": true,
                "(step t1 (cl (not (xor (not p) q)) (not (not p)) (not q)) :rule xor_pos2)": true,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (xor p q) (not p) (not q)) :rule xor_pos2)": false,
                "(step t1 (cl (and p q) (not p) (not q)) :rule xor_pos2)": false,
                "(step t1 (cl (not (xor p q)) p (not q)) :rule xor_pos2)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (xor p q)) (not q) (not q)) :rule xor_pos2)": false,
                "(step t1 (cl (not (xor p q)) (not p) (not p)) :rule xor_pos2)": false,
                "(step t1 (cl (not (xor p (not q))) (not p) q) :rule xor_pos2)": false,
            }
        }
    }

    #[test]
    fn xor_neg1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (xor p q) p (not q)) :rule xor_neg1)": true,
                "(step t1 (cl (xor p (not q)) p (not (not q))) :rule xor_neg1)": true,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (xor p (not q)) p q) :rule xor_neg1)": false,
                "(step t1 (cl (not (xor p q)) p (not q)) :rule xor_neg1)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (xor p q) q (not p)) :rule xor_neg1)": false,
                "(step t1 (cl (xor p q) p (not p)) :rule xor_neg1)": false,
            }
        }
    }

    #[test]
    fn xor_neg2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (xor p q) (not p) q) :rule xor_neg2)": true,
                "(step t1 (cl (xor (not p) q) (not (not p)) q) :rule xor_neg2)": true,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (not (xor p q)) (not p) q) :rule xor_neg2)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (xor p q) (not q) p) :rule xor_neg2)": false,
                "(step t1 (cl (xor p q) (not p) p) :rule xor_neg2)": false,
            }
        }
    }

    #[test]
    fn implies_pos() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (=> p q)) (not p) q) :rule implies_pos)": true,
                "(step t1 (cl (not (=> p (not q))) (not p) (not q)) :rule implies_pos)": true,
                "(step t1 (cl (not (=> (not p) q)) (not (not p)) q) :rule implies_pos)": true,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (=> p q) (not p) q) :rule implies_pos)": false,
                "(step t1 (cl (= p q) (not p) q) :rule implies_pos)": false,
                "(step t1 (cl (not (=> p q)) p q) :rule implies_pos)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (=> p q)) (not q) q) :rule implies_pos)": false,
                "(step t1 (cl (not (=> p q)) (not p) p) :rule implies_pos)": false,
                "(step t1 (cl (not (=> (not p) q)) p q) :rule implies_pos)": false,
            }
        }
    }

    #[test]
    fn implies_neg1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (=> p q) p) :rule implies_neg1)": true,
                "(step t1 (cl (=> (= p q) q) (= p q)) :rule implies_neg1)": true,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (=> p q) p (not q)) :rule implies_neg1)": false,
                "(step t1 (cl (= p q) p) :rule implies_neg1)": false,
                "(step t1 (cl (not (=> p q)) p) :rule implies_neg1)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (=> p q) q) :rule implies_neg1)": false,
                "(step t1 (cl (=> p q) (not p)) :rule implies_neg1)": false,
            }
        }
    }

    #[test]
    fn implies_neg2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (=> p q) (not q)) :rule implies_neg2)": true,
                "(step t1 (cl (=> p (not q)) (not (not q))) :rule implies_neg2)": true,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (=> p q) (not q) p) :rule implies_neg2)": false,
                "(step t1 (cl (= p q) (not q)) :rule implies_neg2)": false,
                "(step t1 (cl (not (=> p q)) (not q)) :rule implies_neg2)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (=> p q) (not p)) :rule implies_neg2)": false,
                "(step t1 (cl (=> p (not q)) q) :rule implies_neg2)": false,
            }
        }
    }

    #[test]
    fn equiv_pos1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (= p q)) p (not q)) :rule equiv_pos1)": true,
                "(step t1 (cl (not (= p (not q))) p (not (not q))) :rule equiv_pos1)": true,
                "(step t1 (cl (not (= (not p) q)) (not p) (not q)) :rule equiv_pos1)": true,
            }
            "Number of terms in clause != 3" {
                "(step t1 (cl (not (= p q)) p) :rule equiv_pos1)": false,
                "(step t1 (cl (not (= p q)) p (not q) q) :rule equiv_pos1)": false,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (= p q) p (not q)) :rule equiv_pos1)": false,
                "(step t1 (cl (and p q) p (not q)) :rule equiv_pos1)": false,
                "(step t1 (cl (not (= p q)) p q) :rule equiv_pos1)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (= p q)) q (not q)) :rule equiv_pos1)": false,
                "(step t1 (cl (not (= p q)) p (not p)) :rule equiv_pos1)": false,
                "(step t1 (cl (not (= (not p) q)) p (not q)) :rule equiv_pos1)": false,
            }
        }
    }

    #[test]
    fn equiv_pos2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (= p q)) (not p) q) :rule equiv_pos2)": true,
                "(step t1 (cl (not (= (not p) q)) (not (not p)) q) :rule equiv_pos2)": true,
                "(step t1 (cl (not (= p (not q))) (not p) (not q)) :rule equiv_pos2)": true,
            }
            "Number of terms in clause != 3" {
                "(step t1 (cl (not (= p q)) (not p)) :rule equiv_pos2)": false,
                "(step t1 (cl (not (= p q)) (not p) q q) :rule equiv_pos2)": false,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (= p q) (not p) q) :rule equiv_pos2)": false,
                "(step t1 (cl (and p q) (not p) q) :rule equiv_pos2)": false,
                "(step t1 (cl (not (= p q)) p q) :rule equiv_pos2)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (= p q)) (not q) q) :rule equiv_pos2)": false,
                "(step t1 (cl (not (= p q)) (not p) p) :rule equiv_pos2)": false,
                "(step t1 (cl (not (= p (not q))) (not p) q) :rule equiv_pos2)": false,
            }
        }
    }

    #[test]
    fn equiv_neg1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (= p q) (not p) (not q)) :rule equiv_neg1)": true,
                "(step t1 (cl (= (not p) q) (not (not p)) (not q)) :rule equiv_neg1)": true,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (= p (not q)) (not p) q) :rule equiv_neg1)": false,
                "(step t1 (cl (not (= p q)) (not p) (not q)) :rule equiv_neg1)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (= p q) (not q) (not p)) :rule equiv_neg1)": false,
                "(step t1 (cl (= p q) (not p) (not p)) :rule equiv_neg1)": false,
            }
        }
    }

    #[test]
    fn equiv_neg2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (= p q) p q) :rule equiv_neg2)": true,
                "(step t1 (cl (= (not p) q) (not p) q) :rule equiv_neg2)": true,
            }
            "Term in clause is not of the correct form" {
                "(step t1 (cl (not (= p q)) p q) :rule equiv_neg2)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (= p q) q p) :rule equiv_neg2)": false,
                "(step t1 (cl (= p q) p p) :rule equiv_neg2)": false,
            }
        }
    }

    #[test]
    fn ite_pos1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (ite p q r)) p r) :rule ite_pos1)": true,
                "(step t1 (cl (not (ite (not p) false (and q r))) (not p) (and q r))
                    :rule ite_pos1)": true,
            }
            "Number of terms in clause != 3" {
                "(step t1 (cl (not (ite p q r)) p) :rule ite_pos1)": false,
                "(step t1 (cl (not (ite p q r)) p q r) :rule ite_pos1)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (ite p q r)) p q) :rule ite_pos1)": false,
                "(step t1 (cl (not (ite p q r)) (not p) r) :rule ite_pos1)": false,
            }
        }
    }

    #[test]
    fn ite_pos2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (ite p q r)) (not p) q) :rule ite_pos2)": true,
                "(step t1 (cl (not (ite (not p) (and q r) false)) (not (not p)) (and q r))
                    :rule ite_pos2)": true,
            }
            "Number of terms in clause != 3" {
                "(step t1 (cl (not (ite p q r)) (not p)) :rule ite_pos2)": false,
                "(step t1 (cl (not (ite p q r)) (not p) q r) :rule ite_pos2)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (ite p q r)) (not p) r) :rule ite_pos2)": false,
                "(step t1 (cl (not (ite p q r)) p q) :rule ite_pos2)": false,
            }
        }
    }

    #[test]
    fn ite_neg1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (ite p q r) p (not r)) :rule ite_neg1)": true,
                "(step t1 (cl (ite (not p) false (and q r)) (not p) (not (and q r)))
                    :rule ite_neg1)": true,
            }
            "Number of terms in clause != 3" {
                "(step t1 (cl (ite p q r) p) :rule ite_neg1)": false,
                "(step t1 (cl (ite p q r) p q (not r)) :rule ite_neg1)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (ite p q r) p r) :rule ite_neg1)": false,
                "(step t1 (cl (ite p q r) (not p) (not r)) :rule ite_neg1)": false,
            }
        }
    }

    #[test]
    fn ite_neg2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (ite p q r) (not p) (not q)) :rule ite_neg2)": true,
                "(step t1 (cl (ite (not p) (and q r) false) (not (not p)) (not (and q r)))
                    :rule ite_neg2)": true,
            }
            "Number of terms in clause != 3" {
                "(step t1 (cl (ite p q r) (not p)) :rule ite_neg2)": false,
                "(step t1 (cl (ite p q r) (not p) (not q) r) :rule ite_neg2)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (ite p q r) (not p) r) :rule ite_neg2)": false,
                "(step t1 (cl (ite p q r) p (not q)) :rule ite_neg2)": false,
                "(step t1 (cl (ite p q r) (not p) q) :rule ite_neg2)": false,
            }
        }
    }

    #[test]
    fn equiv1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (= p q))
                (step t2 (cl (not p) q) :rule equiv1 :premises (h1))": true,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (= p q))
                (step t2 (cl p (not q)) :rule equiv1 :premises (h1))": false,

                "(assume h1 (= p q))
                (step t2 (cl (not p)) :rule equiv1 :premises (h1))": false,

                "(assume h1 (= p q))
                (step t2 (cl (not p) (not q)) :rule equiv1 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn equiv2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (= p q))
                (step t2 (cl p (not q)) :rule equiv2 :premises (h1))": true,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (= p q))
                (step t2 (cl (not p) q) :rule equiv2 :premises (h1))": false,

                "(assume h1 (= p q))
                (step t2 (cl p) :rule equiv2 :premises (h1))": false,

                "(assume h1 (= p q))
                (step t2 (cl p q) :rule equiv2 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_equiv1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not (= p q)))
                (step t2 (cl p q) :rule not_equiv1 :premises (h1))": true,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (not (= p q)))
                (step t2 (cl (not p) q) :rule not_equiv1 :premises (h1))": false,

                "(assume h1 (not (= p q)))
                (step t2 (cl p) :rule not_equiv1 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_equiv2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not (= p q)))
                (step t2 (cl (not p) (not q)) :rule not_equiv2 :premises (h1))": true,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (not (= p q)))
                (step t2 (cl p (not q)) :rule not_equiv2 :premises (h1))": false,

                "(assume h1 (not (= p q)))
                (step t2 (cl (not p)) :rule not_equiv2 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn ite1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun a () Bool)
                (declare-fun b () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (ite p a b))
                (step t2 (cl p b) :rule ite1 :premises (h1))": true,
            }
            "Premise term is not an \"ite\" term" {
                "(assume h1 (or p a b))
                (step t2 (cl p b) :rule ite1 :premises (h1))": false,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (ite p a b))
                (step t2 (cl b p) :rule ite1 :premises (h1))": false,

                "(assume h1 (ite p a b))
                (step t2 (cl p a) :rule ite1 :premises (h1))": false,

                "(assume h1 (ite p a b))
                (step t2 (cl p) :rule ite1 :premises (h1))": false,

                "(assume h1 (ite p a b))
                (step t2 (cl p a b) :rule ite1 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn ite2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun a () Bool)
                (declare-fun b () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (ite p a b))
                (step t2 (cl (not p) a) :rule ite2 :premises (h1))": true,
            }
            "Premise term is not an \"ite\" term" {
                "(assume h1 (or p a b))
                (step t2 (cl (not p) a) :rule ite2 :premises (h1))": false,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (ite p a b))
                (step t2 (cl a (not p)) :rule ite2 :premises (h1))": false,

                "(assume h1 (ite (not p) a b))
                (step t2 (cl p a) :rule ite2 :premises (h1))": false,

                "(assume h1 (ite p a b))
                (step t2 (cl (not p) b) :rule ite2 :premises (h1))": false,

                "(assume h1 (ite p a b))
                (step t2 (cl (not p)) :rule ite2 :premises (h1))": false,

                "(assume h1 (ite p a b))
                (step t2 (cl (not p) a b) :rule ite2 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_ite1() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not (ite p q r)))
                (step t2 (cl p (not r)) :rule not_ite1 :premises (h1))": true,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (not (ite p q r)))
                (step t2 (cl (not p) (not r)) :rule not_ite1 :premises (h1))": false,

                "(assume h1 (not (ite p q r)))
                (step t2 (cl p r) :rule not_ite1 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_ite2() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not (ite p q r)))
                (step t2 (cl (not p) (not q)) :rule not_ite2 :premises (h1))": true,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (not (ite p q r)))
                (step t2 (cl p (not q)) :rule not_ite2 :premises (h1))": false,

                "(assume h1 (not (ite p q r)))
                (step t2 (cl (not p) q) :rule not_ite2 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn ite_intro() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun a () Bool)
                (declare-fun b () Bool)
                (declare-fun c () Bool)
                (declare-fun d () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (=
                    (ite p a b)
                    (and (ite p a b) (ite p (= a (ite p a b)) (= b (ite p a b))))
                )) :rule ite_intro)": true,

                "(step t1 (cl (=
                    (not (ite p a b))
                    (and (not (ite p a b)) (ite p (= a (ite p a b)) (= b (ite p a b))))
                )) :rule ite_intro)": true,
            }
            "Multiple \"ite\" subterms" {
                "(step t1 (cl (=
                    (or (ite p a b) (ite q c d))
                    (and
                        (or (ite p a b) (ite q c d))
                        (ite p (= a (ite p a b)) (= b (ite p a b)))
                        (ite q (= c (ite q c d)) (= d (ite q c d)))
                    )
                )) :rule ite_intro)": true,

                "(step t1 (cl (=
                    (or (ite p a b) (and (ite q c d) (ite (not p) b (not d))))
                    (and
                        (or (ite p a b) (and (ite q c d) (ite (not p) b (not d))))
                        (ite p (= a (ite p a b)) (= b (ite p a b)))
                        (ite q (= c (ite q c d)) (= d (ite q c d)))
                        (ite (not p)
                            (= b (ite (not p) b (not d)))
                            (= (not d) (ite (not p) b (not d))))
                    )
                )) :rule ite_intro)": true,
            }
            "Clause term is not an equality" {
                "(step t1 (cl) :rule ite_intro)": false,
                "(step t1 (cl (not (= p q))) :rule ite_intro)": false,
            }
            "Conjunction is not an \"and\" term" {
                "(step t1 (cl (=
                    (ite p a b)
                    (or (ite p a b) (ite p (= a (ite p a b)) (= b (ite p a b))))
                )) :rule ite_intro)": false,
            }
            "First term in conjunction is not root term" {
                "(step t1 (cl (=
                    (ite p a b)
                    (and q (ite p (= a (ite p a b)) (= b (ite p a b))))
                )) :rule ite_intro)": false,
            }
            "Conjunction has the wrong number of terms" {

                "(step t1 (cl (=
                    (or (ite p a b) (ite q c d))
                    (and
                        (or (ite p a b) (ite q c d))
                        (ite p (= a (ite p a b)) (= b (ite p a b)))
                        (ite q (= c (ite q c d)) (= d (ite q c d)))
                        p
                    )
                )) :rule ite_intro)": false,
            }
            "Right side may equal root term" {
                "(step t1 (cl (= (or a b) (or a b))) :rule ite_intro)": true,
                "(step t1 (cl (= (ite p a b) (ite p a b))) :rule ite_intro)": true,
                "(step t1 (cl (=
                    (and (ite p a b) (or (ite q c d) (ite (not p) b (not d))))
                    (and (ite p a b) (or (ite q c d) (ite (not p) b (not d))))
                )) :rule ite_intro)": true,
            }
            "\"ite\" subterm may be skipped" {
                "(step t1 (cl (=
                    (or (ite p a b) (ite q c d) (ite q d a))
                    (and
                        (or (ite p a b) (ite q c d) (ite q d a))
                        (ite p (= a (ite p a b)) (= b (ite p a b)))
                        (ite q (= d (ite q d a)) (= a (ite q d a)))
                    )
                )) :rule ite_intro)": true,
            }
        }
    }

    #[test]
    fn connective_def() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Case #1" {
                "(step t1 (cl (= (xor p q) (or (and (not p) q) (and p (not q)))))
                    :rule connective_def)": true,
                "(step t1 (cl (= (xor p q) (or (and q (not p)) (and p (not q)))))
                    :rule connective_def)": false,
                "(step t1 (cl (= (xor p q) (or (and p (not q)) (and (not p) q))))
                    :rule connective_def)": false,
            }
            "Case #2" {
                "(step t1 (cl (= (= p q) (and (=> p q) (=> q p)))) :rule connective_def)": true,
                "(step t1 (cl (= (= p q) (and (=> q p) (=> p q)))) :rule connective_def)": false,
            }
            "Case #3" {
                "(step t1 (cl (= (ite p q r) (and (=> p q) (=> (not p) r))))
                    :rule connective_def)": true,
                "(step t1 (cl (= (ite p q r) (and (=> p q) (=> (not p) (not r)))))
                    :rule connective_def)": false,
                "(step t1 (cl (= (ite p q r) (and (=> p r) (=> (not p) q))))
                    :rule connective_def)": false,
            }
            "Case #4" {
                "(step t1 (cl (= (exists ((x Real)) p) (not (forall ((x Real)) (not p)))))
                    :rule connective_def)": true,
                "(step t1 (cl (=
                    (exists ((x Real) (y Real)) (= x y))
                    (not (forall ((x Real) (y Real)) (not (= x y))))
                )) :rule connective_def)": true,
                "(step t1 (cl (= (exists ((x Real)) p) (forall ((x Real)) (not p))))
                    :rule connective_def)": false,
                "(step t1 (cl (= (forall ((x Real)) p) (not (exists ((x Real)) (not p)))))
                    :rule connective_def)": false,
            }
        }
    }
}
