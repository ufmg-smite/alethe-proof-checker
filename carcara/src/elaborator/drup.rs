use super::CheckerError;
use super::*;
use crate::ast::*;
use crate::drup::*;
use indexmap::IndexSet;
use std::collections::HashMap;

pub fn elaborate_drup(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    #[derive(Debug)]
    enum ResolutionStep<'a> {
        Resolvent(
            &'a(bool, Rc<Term>),
            u64,
            u64,
            (Vec<Rc<Term>>, IndexSet<(bool, &'a Rc<Term>)>, u64),
        ),
        UnChanged(IndexSet<(bool, &'a Rc<Term>)>, u64),
    }

    fn resolve<'a>(
        clause1: &IndexSet<(bool, &'a Rc<Term>)>,
        clause2: &IndexSet<(bool, &'a Rc<Term>)>,
        pivot: (bool, &Rc<Term>),
    ) -> IndexSet<(bool, &'a Rc<Term>)> {
        let mut resolvent = IndexSet::new();
        for literal in clause1.union(clause2) {
            if literal.1 == pivot.1 {
                continue;
            }

            resolvent.insert(*literal);
        }

        return resolvent;
    }

    let trace = check_drup(
        pool,
        step.clause.as_slice(),
        step.premises
            .iter()
            .map(|x| x.clause())
            .collect::<Vec<_>>()
            .as_slice(),
        step.args.as_slice(),
    );

    if let Err(err) = trace {
        return Err(CheckerError::DrupFormatError(err));
    }

    let premises: &mut HashMap<u64, _> = &mut step
        .premises
        .iter()
        .map(|p| (hash_term(pool, p.clause()), p.clone()))
        .collect();

    let mut ids = IdHelper::new(&step.id);
    let mut trace = trace.unwrap();
    trace.retain(|x| match x {
        DRupProofAction::Delete(_) => false,
        _ => true,
    });

    for (arg_index, rup_story) in trace.iter().enumerate() {
        match rup_story {
            DRupProofAction::RupStory(rup_clause, rup_history) => {
                let mut rup: Vec<(IndexSet<(bool, &Rc<Term>)>, u64)> = rup_history
                    .iter()
                    .map(|(vec, _, key)| (vec.clone(), *key))
                    .collect();
                let pivots: Vec<_> = rup_history.iter().map(|(_, term, _)| term).collect();

                let mut resolutions = vec![];
                for i in (0..rup_history.len() - 1).rev() {
                    let pivot = pivots[i].as_ref().unwrap();

                    if rup[i + 1].0.contains(&(!pivot.0, &pivot.1)) {
                        let resolvent_indexset: IndexSet<(bool, &Rc<Term>)> =
                            resolve(&rup[i].0, &rup[i + 1].0, (pivot.0, &pivot.1));
                        let resolvent: Vec<Rc<Term>> = resolvent_indexset
                            .iter()
                            .map(|(polarity, term)| {
                                if *polarity {
                                    (*term).clone()
                                } else {
                                    build_term!(pool, (not { (*term).clone() }))
                                }
                            })
                            .collect();

                        let resolvent_hash = hash_term(pool, resolvent.as_slice());

                        resolutions.push(ResolutionStep::Resolvent(
                            pivot,
                            rup[i].1,
                            rup[i + 1].1,
                            (resolvent, resolvent_indexset.clone(), resolvent_hash),
                        ));

                        rup[i] = (resolvent_indexset, resolvent_hash);
                    } else {
                        rup[i] = (rup[i + 1].0.clone(), rup[i + 1].1);
                        resolutions.push(ResolutionStep::UnChanged(rup[i + 1].0.clone(), rup[i].1));
                    }
                }

                match &resolutions[resolutions.len() - 1] {
                    ResolutionStep::Resolvent(_, _, _, (resolvent, _, _)) => {
                        if resolvent.len() > 0 {
                            return Err(CheckerError::DrupFormatError(
                                DrupFormatError::NoFinalBottomInDrup,
                            ));
                        }
                    }
                    ResolutionStep::UnChanged(resolvent, _) => {
                        if resolvent.len() > 0 {
                            return Err(CheckerError::DrupFormatError(
                                DrupFormatError::NoFinalBottomInDrup,
                            ));
                        }
                    }
                }

                resolutions.retain(|step| match step {
                    ResolutionStep::Resolvent(_, _, _, (resolvent, _, _)) => {
                        resolvent.len() > 0 || rup_clause.len() == 0
                    }
                    ResolutionStep::UnChanged(_, _) => false, // Since unchanged are trivally avaliable we can ignore them
                });

                for (i, resolution_step) in resolutions.iter().enumerate() {
                    match resolution_step {
                        ResolutionStep::Resolvent(
                            pivot,
                            c,
                            d,
                            (resolvent, resolvent_indexset, resolvent_hash),
                        ) => {
                            let mut clause = resolvent.clone();
                            let mut hash = *resolvent_hash;

                            let mut proof_step = Rc::new(ProofNode::Step(StepNode {
                                id: ids.next_id(),
                                depth: step.depth,
                                clause: clause,
                                rule: "resolution".to_owned(),
                                premises: vec![
                                    (*premises.get(c).unwrap()).clone(),
                                    (*premises.get(d).unwrap()).clone(),
                                ],
                                discharge: Vec::new(),
                                args: vec![pivot.1.clone(), pool.bool_constant(pivot.0)],
                                previous_step: None,
                            }));

                            if i == resolutions.len() - 1
                                && resolvent_indexset.is_subset(rup_clause) && resolvent_indexset != rup_clause
                            {
                                clause = rup_clause
                                    .iter()
                                    .map(|(polarity, term)| {
                                        if *polarity {
                                            (*term).clone()
                                        } else {
                                            build_term!(pool, (not { (*term).clone() }))
                                        }
                                    })
                                    .collect();
                                hash = hash_term(pool, clause.as_slice());

                                proof_step = Rc::new(ProofNode::Step(StepNode {
                                    id: ids.next_id(),
                                    depth: step.depth,
                                    clause: clause,
                                    rule: "weakening".to_owned(),
                                    premises: vec![proof_step],
                                    discharge: Vec::new(),
                                    args: Vec::new(),
                                    previous_step: None,
                                }));
                            }

                            if i == resolutions.len() - 1 {
                                if arg_index == trace.len() - 1 {
                                    return Ok(proof_step);
                                }
                            }

                            premises.insert(hash, proof_step);
                        }

                        ResolutionStep::UnChanged(_, _) => unreachable!(),
                    }
                }
            }

            DRupProofAction::Delete(_) => unreachable!(),
        }
    }

    unreachable!()
}
