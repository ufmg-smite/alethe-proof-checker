use super::IdHelper;
use crate::{ast::*, resolution::*, utils::DedupIterator};
use std::collections::{HashMap, HashSet};

fn literals_to_clause(pool: &mut dyn TermPool, clause: &[Literal]) -> Vec<Rc<Term>> {
    clause.iter().map(|l| literal_to_term(pool, *l)).collect()
}

struct ResolutionPremise<'a> {
    node: Rc<ProofNode>,
    clause: Vec<Literal<'a>>,
    pivot: Option<(Literal<'a>, bool)>,
}

impl<'a> ResolutionPremise<'a> {
    fn from_step(step: &'a StepNode) -> Vec<Self> {
        let pivots = std::iter::once(None).chain(step.args.chunks(2).map(|chunk| {
            let pivot = chunk[0].remove_all_negations();
            let polarity = chunk[1].is_bool_true();
            Some((pivot, polarity))
        }));
        step.premises
            .iter()
            .zip(pivots)
            .map(|(node, pivot)| {
                let clause = node.clause().iter().map(Rc::remove_all_negations).collect();
                ResolutionPremise { node: node.clone(), clause, pivot }
            })
            .collect()
    }
}

fn apply_naive_resolution<'a>(premises: &[ResolutionPremise<'a>]) -> Vec<Literal<'a>> {
    assert!(premises.len() >= 2);

    let mut current = premises[0].clause.clone();

    for ResolutionPremise { clause, pivot, .. } in &premises[1..] {
        let (pivot, polarity) = pivot.unwrap();

        let negated_pivot = (pivot.0 + 1, pivot.1);
        let (pivot_in_current, pivot_in_next) = if polarity {
            (pivot, negated_pivot)
        } else {
            (negated_pivot, pivot)
        };

        let pos = current.iter().position(|x| x == &pivot_in_current).unwrap();
        current.remove(pos);

        let mut found = false;
        for &t in clause {
            if !found && t == pivot_in_next {
                found = true;
            } else {
                current.push(t);
            }
        }
        assert!(found);
    }

    current
}

pub fn uncrowd_resolution(
    pool: &mut PrimitivePool,
    step: &StepNode,
    rotate_premises: bool,
) -> Rc<ProofNode> {
    let target_conclusion: HashSet<_> = step.clause.iter().map(Rc::remove_all_negations).collect();

    let mut premises = ResolutionPremise::from_step(step);

    let naive_conclusion = apply_naive_resolution(&premises);

    let mut literals_info =
        find_crowding_literals(&naive_conclusion, &target_conclusion, &premises);

    if rotate_premises {
        premises = reorder_premises(&literals_info, premises);
        // Since the premises changed, we recompute the literals info. In theory it might be more
        // efficient to do this as we reorder the premises, but it's very tricky and bug-prone.
        literals_info = find_crowding_literals(&naive_conclusion, &target_conclusion, &premises);
    }

    let mut contractions = find_needed_contractions(literals_info);
    if contractions.last() != Some(&premises.len()) {
        contractions.push(premises.len());
    }

    let mut previous_cut = 0;
    let mut ids = IdHelper::new(&step.id);

    for cut in contractions {
        let (node, clause) = add_partial_resolution_step(
            pool,
            &mut ids,
            step.depth,
            &premises[previous_cut..cut],
            &step.clause,
        );
        premises[cut - 1] = ResolutionPremise { node, clause, pivot: None };
        previous_cut = cut - 1;
    }

    let mut final_step = premises[previous_cut].node.as_step().unwrap().clone();

    if final_step.clause.len() != step.clause.len() {
        let clause = get_weakening_clause(&final_step.clause, &step.clause);
        final_step = StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause,
            rule: "weakening".to_owned(),
            premises: vec![Rc::new(ProofNode::Step(final_step))],
            ..Default::default()
        }
    }

    // We might need to add a reordering step
    if final_step.clause != step.clause {
        assert!(final_step.clause.iter().collect::<HashSet<_>>() == step.clause.iter().collect());
        final_step = StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: "reordering".to_owned(),
            premises: vec![Rc::new(ProofNode::Step(final_step))],
            ..Default::default()
        }
    }

    // To make sure elaboration is idempotent, we need to change the last id to match the original
    // step's id
    final_step.id = step.id.clone();
    Rc::new(ProofNode::Step(final_step))
}

fn add_partial_resolution_step<'a>(
    pool: &mut dyn TermPool,
    ids: &mut IdHelper,
    depth: usize,
    premises: &[ResolutionPremise<'a>],
    final_target: &[Rc<Term>],
) -> (Rc<ProofNode>, Vec<Literal<'a>>) {
    let conclusion = apply_naive_resolution(premises);
    let contracted_conclusion: Vec<_> = conclusion.iter().dedup().copied().collect();

    let needs_contraction = contracted_conclusion.len() != conclusion.len();

    let args: Vec<_> = premises[1..]
        .iter()
        .flat_map(|p| {
            let (literal, polarity) = p.pivot.unwrap();
            [literal_to_term(pool, literal), pool.bool_constant(polarity)]
        })
        .collect();

    let resolution_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: literals_to_clause(pool, &conclusion),
        rule: "resolution".to_owned(),
        premises: premises.iter().map(|p| p.node.clone()).collect(),
        args,
        discharge: Vec::new(),
        previous_step: None,
    }));

    if resolution_step.clause() == final_target {
        return (resolution_step, conclusion);
    }

    if needs_contraction {
        let contracted_clause = resolution_step.clause().iter().dedup().cloned().collect();
        let contraction_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: contracted_clause,
            rule: "contraction".to_owned(),
            premises: vec![resolution_step],
            args: Vec::new(),
            discharge: Vec::new(),
            previous_step: None,
        }));
        (contraction_step, contracted_conclusion)
    } else {
        (resolution_step, conclusion)
    }
}

fn get_weakening_clause(current: &[Rc<Term>], target: &[Rc<Term>]) -> Vec<Rc<Term>> {
    let mut missing: HashMap<&Rc<Term>, usize> = HashMap::new();
    for term in target {
        *missing.entry(term).or_default() += 1;
    }
    for term in current {
        match missing.get_mut(term) {
            Some(0) | None => panic!("current clause is not a subset of target clause!"),
            Some(1) => {
                missing.remove(term);
            }
            Some(count) => *count -= 1,
        }
    }

    let mut result = current.to_vec();
    for (term, n) in missing {
        for _ in 0..n {
            result.push(term.clone());
        }
    }
    result
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct LiteralInfo {
    is_crowding: bool,
    last_inclusion: usize,
    eliminator: usize,

    // Polarity with which the crowding literal appears on the left-hand clause. I.e., `true` if the
    // eliminator literal is the crowding literal +1 negation, `false` if it is -1 negation
    polarity: bool,
}

fn find_crowding_literals<'a>(
    naive_conclusion: &[Literal<'a>],
    target_conclusion: &HashSet<Literal<'a>>,
    premises: &[ResolutionPremise<'a>],
) -> HashMap<Literal<'a>, LiteralInfo> {
    let mut literals: HashMap<_, _> = premises
        .iter()
        .flat_map(|p| &p.clause)
        .map(|l| (*l, LiteralInfo::default()))
        .collect();

    naive_conclusion
        .iter()
        .filter(|lit| !target_conclusion.contains(lit))
        .for_each(|lit| literals.get_mut(lit).unwrap().is_crowding = true);

    for (i, p) in premises.iter().enumerate() {
        for lit in &p.clause {
            if let Some(info) = literals.get_mut(lit) {
                info.last_inclusion = i;
            }
        }
    }
    for (i, p) in premises[1..].iter().enumerate() {
        let (pivot, polarity) = p.pivot.unwrap();
        let pivot_in_current = if polarity {
            pivot
        } else {
            (pivot.0 + 1, pivot.1)
        };
        if let Some(info) = literals.get_mut(&pivot_in_current) {
            if i + 1 > info.last_inclusion {
                info.eliminator = i + 1;
                info.polarity = polarity;
            }
        }
    }
    literals
}

fn find_needed_contractions(literals_info: HashMap<Literal, LiteralInfo>) -> Vec<usize> {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Event {
        Elimination,
        LastInclusion,
    }

    let mut events: Vec<_> = literals_info
        .iter()
        .filter(|(_, info)| info.is_crowding)
        .flat_map(|(lit, info)| {
            [
                (*lit, Event::LastInclusion, info.last_inclusion),
                (*lit, Event::Elimination, info.eliminator),
            ]
        })
        .collect();

    // If there are multiple events at the same index, we must process eliminations first
    events.sort_unstable_by(|(_, a_event, a_index), (_, b_event, b_index)| {
        match a_index.cmp(b_index) {
            std::cmp::Ordering::Equal => a_event.cmp(b_event),
            other => other,
        }
    });

    let mut contractions = Vec::new();
    let mut need_to_contract = HashSet::new();
    for (lit, event, index) in events {
        match event {
            Event::LastInclusion => {
                need_to_contract.insert(lit);
            }
            Event::Elimination => {
                if need_to_contract.contains(&lit) {
                    contractions.push(index);
                    need_to_contract.clear();
                }
            }
        }
    }
    contractions
}

fn reorder_premises<'a>(
    literals_info: &HashMap<Literal, LiteralInfo>,
    mut premises: Vec<ResolutionPremise<'a>>,
) -> Vec<ResolutionPremise<'a>> {
    let mut new_order: Vec<usize> = (0..premises.len()).collect();
    let ordered: Vec<(&Literal, &LiteralInfo)> = {
        let mut v: Vec<_> = literals_info.iter().collect();
        v.sort_unstable_by_key(|(_, info)| info.eliminator);
        v
    };
    for (lit, info) in ordered {
        if !info.is_crowding {
            continue;
        }

        let eliminator_lit = (if info.polarity { lit.0 + 1 } else { lit.0 - 1 }, lit.1);
        let eliminator_premise = &premises[new_order[info.eliminator]];

        let min_elimination_of_non_pivot_literal = eliminator_premise
            .clause
            .iter()
            .filter(|&l| *l != eliminator_lit)
            .map(|l| new_order[literals_info[l].eliminator])
            .min();

        let min_last_inclusion_of_crowding_literal = eliminator_premise
            .clause
            .iter()
            .filter(|&l| *l != eliminator_lit && literals_info[l].is_crowding)
            .map(|l| new_order[literals_info[l].last_inclusion])
            .min();

        let max_safe_move = match (
            min_elimination_of_non_pivot_literal,
            min_last_inclusion_of_crowding_literal,
        ) {
            (None, None) => continue,
            (None, Some(a)) | (Some(a), None) => a,
            (Some(a), Some(b)) => std::cmp::min(a, b),
        };

        let elim = new_order[info.eliminator];
        if max_safe_move > elim {
            new_order[elim..max_safe_move].rotate_left(1);
        }
    }

    new_order
        .iter()
        .map(|&i| {
            let p = &mut premises[i];
            ResolutionPremise {
                node: p.node.clone(),
                clause: std::mem::take(&mut p.clause),
                pivot: p.pivot,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{self, parse_instance, parse_instance_with_pool};

    #[test]
    fn test_uncrowd_resolution() {
        let problem: &[u8] = b"
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const x Bool)
            (declare-const y Bool)
            (declare-const z Bool)
            (declare-const w Bool)
        ";
        let proof = b"
            (step t1 (cl x a b) :rule hole)
            (step t2 (cl (not x) y a c) :rule hole)
            (step t3 (cl (not y) z b) :rule hole)
            (step t4 (cl (not a)) :rule hole)
            (step t5 (cl (not z) c) :rule hole)
            (step t6 (cl d (not b) w) :rule hole)
            (step t7 (cl d (not c)) :rule hole)
            (step t8 (cl (not d)) :rule hole)
            (step t9 (cl w)
                :rule resolution
                :premises (t1 t2 t3 t4 t5 t6 t7 t8)
                :args (x true y true a true z true b true c true d true))
        ";
        let (_, proof, mut pool) = parse_instance(problem, proof, parser::Config::new()).unwrap();
        let proof = ProofNode::from_commands(proof.commands);
        let ProofNode::Step(step) = proof.as_ref() else {
            unreachable!();
        };

        let got = uncrowd_resolution(&mut pool, step, true);

        let expected = b"
            (step t1 (cl x a b) :rule hole)
            (step t2 (cl (not x) y a c) :rule hole)
            (step t3 (cl (not y) z b) :rule hole)
            (step t4 (cl (not a)) :rule hole)
            (step t5 (cl (not z) c) :rule hole)
            (step t6 (cl d (not b) w) :rule hole)
            (step t7 (cl d (not c)) :rule hole)
            (step t8 (cl (not d)) :rule hole)
            (step t9.t1 (cl a b a c z b) :rule resolution :premises (t1 t2 t3)
                :args (x true y true))
            (step t9.t2 (cl a b c z) :rule contraction :premises (t9.t1))
            (step t9.t3 (cl c c d w) :rule resolution :premises (t9.t2 t4 t5 t6)
                :args (a true z true b true))
            (step t9.t4 (cl c d w) :rule contraction :premises (t9.t3))
            (step t9.t5 (cl d w d) :rule resolution :premises (t9.t4 t7) :args (c true))
            (step t9.t6 (cl d w) :rule contraction :premises (t9.t5))
            (step t9 (cl w) :rule resolution :premises (t9.t6 t8) :args (d true))
        ";
        let (_, expected) =
            parse_instance_with_pool(problem, expected, parser::Config::new(), &mut pool).unwrap();
        let expected = ProofNode::from_commands(expected.commands);
        assert!(compare_nodes(&expected, &got));
    }
}
