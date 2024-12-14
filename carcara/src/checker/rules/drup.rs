use super::{CheckerError, RuleArgs, RuleResult};
use crate::ast::*;
use crate::drup::*;

pub fn drup(
    RuleArgs { pool, conclusion, premises, args, .. }: RuleArgs,
) -> RuleResult {
    let premises: Vec<&[Rc<Term>]> = premises
        .iter()
        .map(|p| p.clause)
        .map(|p| p)
        .collect();


    match check_drup(pool, conclusion, premises.as_slice(), args) {
        Ok(_) => Ok(()),
        Err(err) => Err(CheckerError::DrupFormatError(err))
    }
}


#[cfg(test)]
mod tests {
    #[test]
    fn drup() {
        test_cases! {
            definitions = "
                (declare-const a Bool)
                (declare-const b Bool)
                (declare-const c Bool)
                (declare-const d Bool)
                (declare-const e Bool)
            ",
            "Simple working examples" {
                "(assume a0 (or a c))
                (assume a1 (or a (not c) d))
                (assume a2 (or (not d) e))
                (assume a3 (or (not d) (not e)))
                (assume a4 (not a))
                (assume a5 (not b))
                (step t0 (cl a c) :rule or :premises (a0))
                (step t1 (cl a (not c) d) :rule or :premises (a1))
                (step t2 (cl (not d) e) :rule or :premises (a2))
                (step t3 (cl (not d) (not e)) :rule or :premises (a3))
                (step t4 (cl a b) :rule drup :premises (t0 t1 t2 t3) :args ((cl a b)))": true,

                "
                (assume a1 (not a))
                (assume a2 (not b))
                (assume a3 (or a b))
                (step t0 (cl a b) :rule or :premises (a3))
                (step t1 (cl) :rule drup :premises (a1 a2 t0) :args ((cl)))": true,
            }

            "Simple false-working examples" {
                "(assume a0 (or a c))
                (assume a1 (or a (not c) d))
                (assume a2 (or (not d) e))
                (assume a4 (not a))
                (assume a5 (not b))
                (step t0 (cl a c) :rule or :premises (a0))
                (step t1 (cl a (not c) d) :rule or :premises (a1))
                (step t2 (cl (not d) e) :rule or :premises (a2))
                (step t4 (cl a) :rule drup :premises (t0 t1 t2) :args ((cl a b)))": false,

                "
                (assume a1 (not a))
                (assume a3 (or a b))
                (step t0 (cl a b) :rule or :premises (a3))
                (step t1 (cl) :rule drup :premises (a1 t0) :args ((cl)))": false,
            }

        }
    }
}