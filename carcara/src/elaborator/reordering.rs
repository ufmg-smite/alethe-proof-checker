use super::*;
use crate::utils::DedupIterator;

pub fn remove_reorderings(root: &Rc<ProofNode>) -> Rc<ProofNode> {
    let mut modified = HashSet::new();

    mutate(root, |_, node| {
        let Some(step) = node.as_step() else {
            return node.clone();
        };

        if step.rule == "reordering" {
            // Since the premises are changed before the mutation function is called, we have to
            // insert the new node in the modified set
            let new = Rc::new(step.premises[0].as_ref().clone());
            modified.insert(new.clone());
            return new;
        }

        // If the rule is order-sensitive, and any premise was modified, we recompute the conclusion
        if let Some(recompute) = get_recomputation_func(&step.rule) {
            if step.premises.iter().any(|p| modified.contains(p)) {
                let new = Rc::new(ProofNode::Step(StepNode {
                    clause: recompute(step),
                    ..step.clone()
                }));
                modified.insert(new.clone());
                return new;
            }
        }

        node.clone()
    })
}

type RecomputationFunc = fn(&StepNode) -> Vec<Rc<Term>>;

fn get_recomputation_func(rule: &str) -> Option<RecomputationFunc> {
    Some(match rule {
        "weakening" => recompute_weakening,
        "contraction" => recompute_contraction,
        "resolution" | "th_resolution" | "strict_resolution" => recompute_resolution,
        _ => return None,
    })
}

fn recompute_weakening(step: &StepNode) -> Vec<Rc<Term>> {
    let mut new = step.clause.clone();
    let premise = step.premises[0].clause();
    new[..premise.len()].clone_from_slice(premise);
    new
}

fn recompute_contraction(step: &StepNode) -> Vec<Rc<Term>> {
    let new: Vec<_> = step.premises[0].clause().iter().dedup().cloned().collect();
    assert_eq!(step.clause.len(), new.len());
    new
}

fn recompute_resolution(step: &StepNode) -> Vec<Rc<Term>> {
    let premise_clauses: Vec<_> = step.premises.iter().map(|p| p.clause()).collect();
    let pivots: Vec<_> = step
        .args
        .chunks(2)
        .map(|chunk| {
            let pivot = &chunk[0];
            let polarity = chunk[1].is_bool_true();
            (pivot, polarity)
        })
        .collect();
    apply_naive_resolution(&premise_clauses, &pivots)
}

fn apply_naive_resolution(premises: &[&[Rc<Term>]], pivots: &[(&Rc<Term>, bool)]) -> Vec<Rc<Term>> {
    assert!(premises.len() >= 2);
    assert_eq!(pivots.len(), premises.len() - 1);

    let mut current = premises[0].to_vec();

    for (&premise, &(pivot, polarity)) in premises[1..].iter().zip(pivots) {
        let is_pivot = |x: &Rc<Term>, is_current: bool| {
            if is_current == polarity {
                x == pivot
            } else {
                x.remove_negation() == Some(pivot)
            }
        };

        let pos = current.iter().position(|x| is_pivot(x, true)).unwrap();
        current.remove(pos);

        let mut found = false;
        for t in premise {
            if !found && is_pivot(t, false) {
                found = true;
            } else {
                current.push(t.clone());
            }
        }
        assert!(found);
    }

    current
}
