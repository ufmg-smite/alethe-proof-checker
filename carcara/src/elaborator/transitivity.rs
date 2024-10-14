use super::IdHelper;
use crate::{ast::*, checker::error::CheckerError};

fn add_symm_step(pool: &mut PrimitivePool, node: &Rc<ProofNode>, id: String) -> Rc<ProofNode> {
    assert_eq!(node.clause().len(), 1);
    let (a, b) = match_term!((= a b) = node.clause()[0]).unwrap();
    let clause = vec![build_term!(pool, (= {b.clone()} {a.clone()}))];
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth: node.depth(),
        clause,
        rule: "symm".into(),
        premises: vec![node.clone()],
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}

/// Similar to `find_chain`, but reorders a premises vector to match the found chain. In `trans`,
/// this is used to reorder the step premises vector; in `eq_transitive`, it is used to reorder the
/// clause. This returns a boolean indicating whether any reordering was needed, a `usize`
/// indicating how many premises are needed to prove the conclusion, and a vector of indices of the
/// premise equalities that need to be flipped.
fn find_and_trace_chain<'a, T>(
    mut conclusion: (&'a Rc<Term>, &'a Rc<Term>),
    premise_equalities: &mut [(&'a Rc<Term>, &'a Rc<Term>)],
    premises: &mut [T],
) -> Result<(bool, usize, Vec<usize>), CheckerError> {
    let mut reordered = false;
    let mut should_flip = Vec::with_capacity(premise_equalities.len());
    let mut i = 0;
    loop {
        if conclusion.0 == conclusion.1 {
            return Ok((reordered, i, should_flip));
        }

        let (found_index, next_link) = premise_equalities[i..]
            .iter()
            .enumerate()
            .find_map(|(j, &(t, u))| {
                if t == conclusion.0 {
                    Some((j + i, u))
                } else if u == conclusion.0 {
                    should_flip.push(i);
                    Some((j + i, t))
                } else {
                    None
                }
            })
            .ok_or_else(|| {
                let (a, b) = conclusion;
                CheckerError::BrokenTransitivityChain(a.clone(), b.clone())
            })?;

        if found_index != i {
            premise_equalities.swap(i, found_index);
            premises.swap(i, found_index);
            reordered = true;
        }
        conclusion = (next_link, conclusion.1);
        i += 1;
    }
}

pub fn trans(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);

    let conclusion_equality = match_term_err!((= t u) = &step.clause[0])?;
    let mut premise_equalities: Vec<_> = step
        .premises
        .iter()
        .map(|premise| {
            assert_eq!(premise.clause().len(), 1);
            match_term_err!((= t u) = &premise.clause()[0])
        })
        .collect::<Result<_, _>>()?;

    let mut new_premises = step.premises.clone();
    let (_, num_needed, should_flip) = find_and_trace_chain(
        conclusion_equality,
        &mut premise_equalities,
        &mut new_premises,
    )?;

    // If there are any premises in the step which are not needed to complete the transitivity
    // chain, we simply remove them in the elaborated step.
    new_premises.truncate(num_needed);

    // If there are any premises that need flipping, we need to introduce `symm` steps to flip the
    // needed equalities
    let mut ids = IdHelper::new(&step.id);
    for i in should_flip {
        new_premises[i] = add_symm_step(pool, &new_premises[i], ids.next_id());
    }

    Ok(Rc::new(ProofNode::Step(StepNode {
        premises: new_premises,
        ..step.clone()
    })))
}

pub fn eq_transitive(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    let n = step.clause.len();
    assert!(n > 2);

    // The last term in the conclusion clause should be an equality, and it will be the conclusion
    // of the transitive chain
    let conclusion_equality = match_term_err!((= t u) = step.clause.last().unwrap())?;

    // The first `conclusion.len()` - 1 terms in the conclusion clause must be a sequence of
    // inequalities, and they will be the premises of the transitive chain
    let mut premise_equalities: Vec<_> = step.clause[..n - 1]
        .iter()
        .map(|term| match_term_err!((not (= t u)) = term))
        .collect::<Result<_, _>>()?;

    let mut new_clause: Vec<_> = step.clause.clone();
    let (needs_reordering, num_needed, should_flip) = find_and_trace_chain(
        conclusion_equality,
        &mut premise_equalities,
        &mut new_clause[..n - 1],
    )?;

    if !needs_reordering && num_needed == n - 1 && should_flip.is_empty() {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    for &i in &should_flip {
        new_clause[i] = if let Some((a, b)) = match_term!((not (= a b)) = &new_clause[i]) {
            build_term!(pool, (not (= {b.clone()} {a.clone()})))
        } else {
            panic!()
        };
    }

    let not_needed = if num_needed == n - 1 {
        Vec::new()
    } else {
        let conclusion = new_clause.pop().unwrap();
        let not_needed = new_clause.split_off(num_needed);
        new_clause.push(conclusion);
        not_needed
    };

    let mut ids = IdHelper::new(&step.id);

    let new_eq_transitive_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: new_clause,
        rule: "eq_transitive".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }));

    let mut latest_step = new_eq_transitive_step.clone();

    if !should_flip.is_empty() {
        latest_step = flip_eq_transitive_premises(
            pool,
            new_eq_transitive_step,
            step.depth,
            latest_step.clause(),
            &should_flip,
            &mut ids,
        );
    }

    if !not_needed.is_empty() {
        let mut clause = latest_step.clause().to_vec();
        clause.extend(not_needed);
        latest_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause,
            rule: "weakening".to_owned(),
            premises: vec![latest_step],
            args: Vec::new(),
            discharge: Vec::new(),
            previous_step: None,
        }));
    }

    Ok(Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "reordering".to_owned(),
        premises: vec![latest_step],
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    })))
}

fn flip_eq_transitive_premises(
    pool: &mut dyn TermPool,
    new_eq_transitive_step: Rc<ProofNode>,
    depth: usize,
    new_clause: &[Rc<Term>],
    should_flip: &[usize],
    ids: &mut IdHelper,
) -> Rc<ProofNode> {
    let resolution_pivots: Vec<_> = should_flip
        .iter()
        .map(|&i| {
            let (a, b) = match_term!((not (= a b)) = new_clause[i]).unwrap();

            let a_eq_b = build_term!(pool, (= {a.clone()} {b.clone()}));
            let b_eq_a = build_term!(pool, (= {b.clone()} {a.clone()}));
            let eq_symm_step = Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth,
                clause: vec![build_term!(pool, (= {a_eq_b.clone()} {b_eq_a.clone()}))],
                rule: "eq_symmetric".to_owned(),
                ..StepNode::default()
            }));

            let not_b_eq_a = build_term!(pool, (not {(b_eq_a)}));
            let equiv2_step = Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth,
                clause: vec![a_eq_b.clone(), not_b_eq_a.clone()],
                rule: "equiv2".to_owned(),
                premises: vec![eq_symm_step],
                ..StepNode::default()
            }));

            (equiv2_step, a_eq_b, not_b_eq_a)
        })
        .collect();

    let clause = {
        let should_flip = {
            let mut new = vec![false; new_clause.len()];
            for &i in should_flip {
                new[i] = true;
            }
            new
        };
        let mut original: Vec<_> = new_clause
            .iter()
            .enumerate()
            .filter(|&(i, _)| !should_flip[i])
            .map(|(_, t)| t.clone())
            .collect();
        original.extend(
            resolution_pivots
                .iter()
                .map(|(_, _, to_introduce)| to_introduce.clone()),
        );
        original
    };
    let mut premises = vec![new_eq_transitive_step];
    premises.extend(resolution_pivots.iter().map(|(index, _, _)| index.clone()));
    let args: Vec<_> = resolution_pivots
        .into_iter()
        .flat_map(|(_, pivot, _)| [pivot, pool.bool_false()])
        .collect();

    Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause,
        rule: "resolution".to_owned(),
        premises,
        args,
        discharge: Vec::new(),
        previous_step: None,
    }))
}
