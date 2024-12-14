use crate::ast::*;
use core::panic;
use indexmap::IndexSet;
use std::borrow::{Borrow, BorrowMut};
use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use thiserror::Error;

#[derive(Debug)]
pub enum Implied<T, X> {
    Pivot(T, X),
    Bottom(X),
    NotUnsat(),
}

pub type RupAdition<'a> = Vec<(
    IndexSet<(bool, &'a Rc<Term>)>,
    Option<(bool, Rc<Term>)>,
    u64,
)>;

pub enum DRupProofAction<'a> {
    RupStory(IndexSet<(bool, &'a Rc<Term>)>, RupAdition<'a>),
    Delete(&'a [Rc<Term>]),
}

pub type DRupStory<'a> = Vec<DRupProofAction<'a>>;

#[derive(Debug, Error)]
pub enum DrupFormatError {
    #[error("couldn't find conclusion term in the premise clauses")]
    NoConclusionInPremise,
    #[error(
        "couldn't elaborate drup because bottom wasn't derived from the premises and the argument"
    )]
    NoFinalBottomInDrup,
    #[error("couldn't elaborate drup because the argument might not be in RUP")]
    PotentialNoDrupFormat,
}

pub fn hash_term<T: Borrow<Rc<Term>>>(pool: &mut dyn TermPool, term: &[T]) -> u64 {
    let mut term = term
        .iter()
        .map(|literal| {
            let (p, regular_term): (bool, &Rc<Term>) =
                (literal.borrow()).remove_all_negations_with_polarity();
            if p {
                return regular_term.clone();
            } else {
                return build_term!(pool, (not { (*regular_term).clone() }))
            };
        })
        .collect::<Vec<_>>();

    term.sort_by(|x, y| {
        let mut s = DefaultHasher::new();
        let mut s2 = DefaultHasher::new();
        x.hash(&mut s);
        y.hash(&mut s2);

        return s.finish().cmp(&s2.finish());
    });

    let mut s = DefaultHasher::new();
    for literal in term {
        literal.hash(&mut s);
    }

    let hash = s.finish();
    return hash;
}

fn get_implied_clause<'a>(
    clauses: &mut Vec<(
        (Option<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>),
        (IndexSet<(bool, &'a Rc<Term>)>, u64),
    )>,
    env: &HashMap<(bool, Rc<Term>), bool>,
) -> Implied<(bool, Rc<Term>), (IndexSet<(bool, &'a Rc<Term>)>, u64)> {
    if clauses.is_empty() {
        return Implied::NotUnsat();
    }

    for (schema, (lits, key)) in clauses {
        match schema {
            (None, None) => return Implied::Bottom(((*lits).clone(), *key)),

            (Some((b, t)), None) | (None, Some((b, t))) => match env.get(&(*b, (*t).clone())) {
                Some(false) => {
                    assert_eq!(lits.len(), 1);
                    return Implied::Bottom(((*lits).clone(), *key));
                }
                Some(true) => continue,
                None => {
                    assert_eq!(lits.len(), 1);
                    return Implied::Pivot((*b, (*t).clone()), ((*lits).clone(), *key));
                }
            },

            (Some((b, t)), Some((b0, t0))) => {
                match (env.get(&(*b, (*t).clone())), env.get(&(*b0, (*t0).clone()))) {
                    (Some(true), _) => continue,
                    (_, Some(true)) => continue,
                    (None, None) => continue,
                    (_, _) => {
                        let mut unset_literal = None;
                        let mut not_unit = false;

                        for (b1, t1) in lits.iter() {
                            let assign_state = env.get(&(*b1, (*t1).clone()));

                            match assign_state {
                                None => {
                                    let literal = Some((*b1, (*t1).clone()));
                                    if schema.0 != literal && schema.1 != literal {
                                        if schema.0 != None {
                                            schema.0 = literal;
                                        } else if schema.1 != None {
                                            schema.1 = literal;
                                        }
                                    }

                                    if unset_literal.is_some() {
                                        not_unit = true;
                                        continue;
                                    }

                                    unset_literal = Some((b1, (*t1).clone()));
                                }
                                Some(true) => {
                                    // Set the true clause as a watched literal to avoid searching O(n) in this "deleted" clause
                                    let literal = Some((*b1, (*t1).clone()));
                                    if schema.0 != literal && schema.1 != literal {
                                        if schema.0 != None {
                                            schema.0 = literal;
                                        } else if schema.1 != None {
                                            schema.1 = literal;
                                        }
                                    }

                                    not_unit = true;
                                    continue;
                                }
                                Some(false) => (),
                            }
                        }

                        if not_unit {
                            continue;
                        }

                        return match unset_literal {
                            Some((p, polarity)) => {
                                Implied::Pivot((*p, polarity.clone()), ((*lits).clone(), *key))
                            }
                            _ => Implied::Bottom(((*lits).clone(), *key)),
                        };
                    }
                }
            }
        }
    }
    Implied::NotUnsat()
}

fn rup<'a>(
    pool: &mut dyn TermPool,
    drup_clauses: &HashMap<u64, IndexSet<(bool, &'a Rc<Term>)>>,
    goal: &'a [Rc<Term>],
) -> Option<RupAdition<'a>> {
    let mut unit_story: RupAdition<'a> = vec![];

    let mut clauses: Vec<(
        (Option<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>),
        (IndexSet<(bool, &'a Rc<Term>)>, u64),
    )> = vec![];

    let mut env: HashMap<(bool, Rc<Term>), bool> = HashMap::new();

    for term in goal {
        let (p, regular_term) = term.remove_all_negations_with_polarity();
        let mut clause: IndexSet<(bool, &Rc<Term>)> = IndexSet::new();
        clause.insert((!p, regular_term));
        clauses.push((
            (Some((!p, regular_term.clone())), None),
            (clause, hash_term(pool, vec![term].as_slice())),
        ));
    }

    for (key, clause) in drup_clauses {
        let mut watched_literals = clause.iter().take(2);
        clauses.push((
            (
                watched_literals.next().map(|v| (v.0, (*v.1).clone())),
                watched_literals.next().map(|v| (v.0, (*v.1).clone())),
            ),
            (clause.clone(), *key),
        ));
    }

    loop {
        let unit = get_implied_clause(clauses.borrow_mut(), env.borrow());
        match unit {
            Implied::Bottom(clause) => {
                unit_story.push((clause.0, None, clause.1));
                return Some(unit_story);
            }
            Implied::Pivot(literal, clause) => {
                env.insert(literal.clone(), true);
                let negated_literal = (!literal.0, literal.1.clone());
                env.insert(negated_literal.clone(), false);
                unit_story.push((clause.0, Some((literal.0, literal.1)), clause.1));
            }
            Implied::NotUnsat() => return None,
        }
    }
}

pub fn check_drup<'a>(
    pool: &mut dyn TermPool,
    conclusion: &'a[Rc<Term>],
    premises: &[&'a [Rc<Term>]],
    args: &'a[Rc<Term>],
) -> Result<DRupStory<'a>, DrupFormatError> {
    let mut premises: HashMap<u64, _> = premises
        .iter()
        .map(|p| {
            (
                hash_term(pool, p),
                p.iter()
                    .map(Rc::remove_all_negations_with_polarity)
                    .collect::<IndexSet<_>>(),
            )
        })
        .collect();

    let mut drup_history: DRupStory = vec![];
    for t in args {
        match match_term!((delete (cl ...)) = &t) {
            Some(terms) => {
                premises.remove(&hash_term(pool, terms));
                drup_history.push(DRupProofAction::Delete(terms));
                continue;
            }
            None => (),
        }

        let terms = match match_term!((cl ...) = &t) {
            Some(terms) => terms,
            None => panic!("Invalid clause term"),
        };
        let unit_history = rup(pool, premises.borrow(), terms);

        if unit_history == None {
            return Err(DrupFormatError::NoFinalBottomInDrup);
        }

        let terms_indexed_set = terms
            .iter()
            .map(Rc::remove_all_negations_with_polarity)
            .collect::<IndexSet<_>>();

        drup_history.push(DRupProofAction::RupStory(
            terms_indexed_set.clone(),
            unit_history.unwrap(),
        ));

        premises.insert(hash_term(pool, terms), terms_indexed_set);
    }

    if !premises.contains_key(&hash_term(pool, conclusion)) {
        return Err(DrupFormatError::NoConclusionInPremise);
    }

    Ok(drup_history)
}
