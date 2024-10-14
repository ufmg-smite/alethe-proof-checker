use super::*;
use crate::{ast::*, checker::error::CheckerError, resolution::*, utils::DedupIterator};

pub fn resolution(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    let mut ids = IdHelper::new(&step.id);

    // In the cases where the rule is used to get an empty clause from `(not true)`, we add a `true`
    // step to get an actual resolution step
    if step.clause.is_empty() && step.premises.len() == 1 {
        if let [t] = step.premises[0].clause() {
            if match_term!((not true) = t).is_some() {
                let true_step = Rc::new(ProofNode::Step(StepNode {
                    id: ids.next_id(),
                    depth: step.depth,
                    clause: vec![pool.bool_true()],
                    rule: "true".to_owned(),
                    ..Default::default()
                }));

                return Ok(Rc::new(ProofNode::Step(StepNode {
                    id: ids.next_id(),
                    depth: step.depth,
                    clause: Vec::new(),
                    rule: "resolution".to_owned(),
                    premises: vec![step.premises[0].clone(), true_step],
                    args: [true, false].map(|a| pool.bool_constant(a)).to_vec(),
                    ..Default::default()
                })));
            }
        }
    }

    // In some cases, due to a bug in veriT, a resolution step will conclude the empty clause, and
    // will have multiple premises, of which one has an empty clause as its conclusion. The checker
    // can already deal with this case safely, but not the elaborator, so if we detect it we skip
    // elaborating this step. Either way, since this step has a premise which concludes the empty
    // clause, it is not actually necessary, and will be pruned during post-processing.
    if step.clause.is_empty() {
        for p in &step.premises {
            if p.clause().is_empty() {
                return Ok(Rc::new(ProofNode::Step(step.clone())));
            }
        }
    }

    let mut premises: Vec<_> = step.premises.iter().dedup().cloned().collect();
    let premise_clauses: Vec<_> = premises.iter().map(|p| p.clause()).collect();

    let ResolutionTrace { not_not_added, pivot_trace } =
        greedy_resolution(&step.clause, &premise_clauses, pool, true).or_else(|_| {
            premises.reverse();
            let premise_clauses: Vec<_> = premises.iter().map(|p| p.clause()).collect();
            greedy_resolution(&step.clause, &premise_clauses, pool, true)
        })?;

    let pivots = pivot_trace
        .into_iter()
        .flat_map(|(pivot, polarity)| [pivot, pool.bool_constant(polarity)])
        .collect();

    let mut resolution_step = StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "resolution".to_owned(),
        premises,
        args: pivots,
        ..Default::default()
    };

    if not_not_added {
        // In this case, where the solver added a double negation implicitly to the concluded term,
        // we remove it from the resolution conclusion, and then add a series of steps to
        // reconstruct it again. More precisely, if the conclusion of the resolution step should
        // have been `c`, but was instead `(not (not c))`, we will have:
        //
        // ```
        // (step t1 (cl (not (not c))) :rule resolution :premises ...)
        // ```
        //
        // which will become:
        //
        // ```
        // (step t1 (cl c) :rule resolution :premises ...)
        // (step t1.t2 (cl (not (not (not (not c)))) (not c)) :rule not_not)
        // (step t1.t3 (cl (not (not (not (not (not c))))) (not (not c))) :rule not_not)
        // (step t1.t4 (cl (not (not c))) :rule resolution :premises (t1 t1.t2 t1.t3)
        //     :args (c true (not (not (not (not c)))) true))
        // ```

        assert!(resolution_step.clause.len() == 1);
        let original_conclusion = resolution_step.clause;
        let double_not_c = original_conclusion[0].clone();
        let single_not_c = double_not_c.remove_negation().unwrap().clone();
        let c = single_not_c.remove_negation().unwrap().clone();
        let quadruple_not_c = build_term!(pool, (not (not {double_not_c.clone()})));
        let quintuple_not_c = build_term!(pool, (not {quadruple_not_c.clone()}));

        // First, we change the conclusion of the resolution step
        resolution_step.clause = vec![c.clone()];
        let resolution_step = Rc::new(ProofNode::Step(resolution_step));

        // Then we add the two `not_not` steps
        let first_not_not_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![quadruple_not_c.clone(), single_not_c],
            rule: "not_not".to_owned(),
            ..Default::default()
        }));

        let second_not_not_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![quintuple_not_c, double_not_c.clone()],
            rule: "not_not".to_owned(),
            ..Default::default()
        }));

        // Finally, we add a new resolution step, refering to the preivous three, and concluding the
        // original resolution step's conclusion
        let args = [c, pool.bool_true(), quadruple_not_c, pool.bool_true()]
            .into_iter()
            .collect();

        Ok(Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![double_not_c],
            rule: "resolution".to_owned(),
            premises: vec![resolution_step, first_not_not_step, second_not_not_step],
            args,
            ..Default::default()
        })))
    } else {
        Ok(Rc::new(ProofNode::Step(resolution_step)))
    }
}
