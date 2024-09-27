mod hole;
mod lia_generic;
mod polyeq;
mod reflexivity;
mod reordering;
mod resolution;
mod transitivity;
mod uncrowding;

use crate::{ast::*, CheckerError};
use indexmap::IndexSet;
use polyeq::PolyeqElaborator;
use std::{
    collections::{HashMap, HashSet},
    time::{Duration, Instant},
};

#[derive(Debug, Clone)]
pub struct Config {
    /// If `Some`, enables the elaboration of `lia_generic` steps using an external solver. When
    /// checking a proof, this means calling the solver to solve the linear integer arithmetic
    /// problem, checking the proof, and discarding it. When elaborating, the proof will instead be
    /// inserted in the place of the `lia_generic` step. See [`LiaGenericOptions`] for more details.
    pub lia_options: Option<LiaGenericOptions>,

    /// Enables an optimization that reorders premises when uncrowding resolution steps, in order to
    /// further minimize the number of `contraction` steps added.
    pub uncrowd_rotation: bool,

    pub hole_options: Option<HoleOptions>,
}

#[derive(Debug, Clone, Copy)]
pub enum ElaborationStep {
    Polyeq,
    LiaGeneric,
    Local,
    Uncrowd,
    Reordering,
    Hole,
}

/// The options that control how `lia_generic` steps are elaborated using an external solver.
#[derive(Debug, Clone)]
pub struct LiaGenericOptions {
    /// The external solver path. The solver should be a binary that can read SMT-LIB from stdin and
    /// output an Alethe proof to stdout.
    pub solver: Box<str>,

    /// The arguments to pass to the solver.
    pub arguments: Vec<Box<str>>,
}

/// The options that control how `hole` steps are elaborated using an external solver.
#[derive(Debug, Clone)]
pub struct HoleOptions {
    /// The external solver path. The solver should be a binary that can read SMT-LIB from stdin and
    /// output an Alethe proof to stdout.
    pub solver: Box<str>,

    /// The arguments to pass to the solver.
    pub arguments: Vec<Box<str>>,
}

pub struct Elaborator<'e> {
    pool: &'e mut PrimitivePool,
    problem: &'e Problem,
    config: Config,
}

impl<'e> Elaborator<'e> {
    pub fn new(pool: &'e mut PrimitivePool, problem: &'e Problem, config: Config) -> Self {
        Self { pool, problem, config }
    }

    pub fn elaborate_with_default_pipeline(&mut self, root: &Rc<ProofNode>) -> Rc<ProofNode> {
        use ElaborationStep::*;
        let pipeline = vec![Polyeq, LiaGeneric, Local, Uncrowd, Reordering];
        self.elaborate(root, pipeline)
    }

    pub fn elaborate(
        &mut self,
        root: &Rc<ProofNode>,
        pipeline: Vec<ElaborationStep>,
    ) -> Rc<ProofNode> {
        self.elaborate_with_stats(root, pipeline).0
    }

    pub fn elaborate_with_stats(
        &mut self,
        root: &Rc<ProofNode>,
        pipeline: Vec<ElaborationStep>,
    ) -> (Rc<ProofNode>, Vec<Duration>) {
        let mut durations = Vec::new();
        let mut current = root.clone();
        for step in pipeline {
            let time = Instant::now();
            current = match step {
                ElaborationStep::Polyeq => self.elaborate_polyeq(&current),
                ElaborationStep::LiaGeneric if self.config.lia_options.is_some() => {
                    mutate(&current, |_, node| match node.as_ref() {
                        ProofNode::Step(s) if s.rule == "lia_generic" => {
                            lia_generic::lia_generic(self, s).unwrap_or_else(|| node.clone())
                        }
                        _ => node.clone(),
                    })
                }
                ElaborationStep::LiaGeneric => current.clone(),
                ElaborationStep::Local => self.elaborate_local(&current),
                ElaborationStep::Uncrowd => mutate(&current, |_, node| match node.as_ref() {
                    ProofNode::Step(s)
                        if (s.rule == "resolution" || s.rule == "th_resolution")
                            && !s.args.is_empty() =>
                    {
                        uncrowding::uncrowd_resolution(self.pool, s, self.config.uncrowd_rotation)
                    }
                    _ => node.clone(),
                }),
                ElaborationStep::Reordering => reordering::remove_reorderings(&current),
                ElaborationStep::Hole => {
                    if self.config.hole_options.is_none() {
                        current.clone()
                    } else {
                        mutate(&current, |_, node| match node.as_ref() {
                            ProofNode::Step(s)
                                if (s.rule == "all_simplify" || s.rule == "rare_rewrite") =>
                            {
                                hole::hole(self, s).unwrap_or_else(|| node.clone())
                            }
                            _ => node.clone(),
                        })
                    }
                }
            };
            durations.push(time.elapsed());
        }
        (current, durations)
    }

    fn elaborate_polyeq(&mut self, root: &Rc<ProofNode>) -> Rc<ProofNode> {
        mutate(root, |context, node| {
            match node.as_ref() {
                ProofNode::Assume { id, depth, term }
                    if context.is_empty() && !self.problem.premises.contains(term) =>
                {
                    self.elaborate_assume(id, *depth, term)
                }
                ProofNode::Step(s) if s.rule == "refl" => {
                    reflexivity::refl(self.pool, context, s).unwrap() // TODO: add proper error handling
                }
                _ => node.clone(),
            }
        })
    }

    fn elaborate_local(&mut self, root: &Rc<ProofNode>) -> Rc<ProofNode> {
        fn get_elaboration_function(rule: &str) -> Option<ElaborationFunc> {
            Some(match rule {
                "eq_transitive" => transitivity::eq_transitive,
                "trans" => transitivity::trans,
                "resolution" | "th_resolution" => resolution::resolution,
                _ => return None,
            })
        }

        mutate(root, |context, node| {
            match node.as_ref() {
                ProofNode::Step(s) => {
                    if let Some(func) = get_elaboration_function(&s.rule) {
                        return func(self.pool, context, s).unwrap(); // TODO: add proper error handling
                    }
                }
                ProofNode::Subproof(_) => unreachable!(),
                ProofNode::Assume { .. } => (),
            }
            node.clone()
        })
    }

    fn elaborate_assume(&mut self, id: &str, depth: usize, term: &Rc<Term>) -> Rc<ProofNode> {
        let mut found = None;
        for p in &self.problem.premises {
            if Polyeq::new()
                .mod_reordering(true)
                .mod_nary(true)
                .eq(term, p)
            {
                found = Some(p.clone());
                break;
            }
        }
        let premise = found.expect("trying to elaborate assume, but it is invalid!");

        let new_assume = Rc::new(ProofNode::Assume {
            id: id.to_owned(),
            depth,
            term: premise.clone(),
        });

        let mut ids = IdHelper::new(id);
        let equality_step = PolyeqElaborator::new(&mut ids, depth, false).elaborate(
            self.pool,
            premise.clone(),
            term.clone(),
        );

        let equiv1_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: vec![
                build_term!(self.pool, (not {premise.clone()})),
                term.clone(),
            ],
            rule: "equiv1".to_owned(),
            premises: vec![equality_step],
            ..Default::default()
        }));

        Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: vec![term.clone()],
            rule: "resolution".to_owned(),
            premises: vec![new_assume, equiv1_step],
            args: vec![
                ProofArg::Term(premise),
                ProofArg::Term(self.pool.bool_true()),
            ],
            ..Default::default()
        }))
    }
}

pub fn add_refl_step(
    pool: &mut dyn TermPool,
    a: Rc<Term>,
    b: Rc<Term>,
    id: String,
    depth: usize,
) -> Rc<ProofNode> {
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth,
        clause: vec![build_term!(pool, (= {a} {b}))],
        rule: "refl".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}

type ElaborationFunc =
    fn(&mut PrimitivePool, &mut ContextStack, &StepNode) -> Result<Rc<ProofNode>, CheckerError>;

fn mutate<F>(root: &Rc<ProofNode>, mut mutate_func: F) -> Rc<ProofNode>
where
    F: FnMut(&mut ContextStack, &Rc<ProofNode>) -> Rc<ProofNode>,
{
    let mut cache: HashMap<&Rc<ProofNode>, Rc<ProofNode>> = HashMap::new();
    let mut did_outbound: HashSet<&Rc<ProofNode>> = HashSet::new();
    let mut todo = vec![(root, false)];

    let mut outbound_premises_stack = vec![IndexSet::new()];
    let mut context = ContextStack::new();

    while let Some((node, is_done)) = todo.pop() {
        if cache.contains_key(node) {
            continue;
        }

        let mutated = match node.as_ref() {
            ProofNode::Assume { .. } => mutate_func(&mut context, node),
            ProofNode::Step(s) if !is_done => {
                todo.push((node, true));

                let all_premises = s
                    .premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(&s.previous_step)
                    .rev();
                todo.extend(
                    all_premises.filter_map(|p| (!cache.contains_key(p)).then_some((p, false))),
                );

                continue;
            }
            ProofNode::Step(s) => {
                let premises: Vec<_> = s.premises.iter().map(|p| cache[p].clone()).collect();
                let discharge: Vec<_> = s.discharge.iter().map(|p| cache[p].clone()).collect();
                let previous_step = s.previous_step.as_ref().map(|p| cache[p].clone());

                let new_node = Rc::new(ProofNode::Step(StepNode {
                    premises,
                    discharge,
                    previous_step,
                    ..s.clone()
                }));
                mutate_func(&mut context, &new_node)
            }
            ProofNode::Subproof(s) if !is_done => {
                assert!(
                    node.depth() == outbound_premises_stack.len() - 1,
                    "all outbound premises should have already been dealt with!"
                );

                if !did_outbound.contains(node) {
                    did_outbound.insert(node);
                    todo.push((node, false));
                    todo.extend(s.outbound_premises.iter().map(|premise| (premise, false)));
                    continue;
                }

                todo.push((node, true));
                todo.push((&s.last_step, false));
                outbound_premises_stack.push(IndexSet::new());
                context.push(&s.args);
                continue;
            }
            ProofNode::Subproof(s) => {
                context.pop();
                let outbound_premises =
                    outbound_premises_stack.pop().unwrap().into_iter().collect();
                Rc::new(ProofNode::Subproof(SubproofNode {
                    last_step: cache[&s.last_step].clone(),
                    args: s.args.clone(),
                    outbound_premises,
                }))
            }
        };
        outbound_premises_stack
            .last_mut()
            .unwrap()
            .extend(mutated.get_outbound_premises());
        cache.insert(node, mutated);
    }
    assert!(outbound_premises_stack.len() == 1 && outbound_premises_stack[0].is_empty());
    cache[root].clone()
}

struct IdHelper {
    root: String,
    stack: Vec<usize>,
}

impl IdHelper {
    fn new(root: &str) -> Self {
        Self {
            root: root.to_owned(),
            stack: vec![0],
        }
    }

    fn next_id(&mut self) -> String {
        use std::fmt::Write;

        let mut current = self.root.clone();
        for i in &self.stack {
            write!(&mut current, ".t{}", i + 1).unwrap();
        }
        *self.stack.last_mut().unwrap() += 1;
        current
    }

    fn push(&mut self) {
        self.stack.push(0);
    }

    fn pop(&mut self) {
        assert!(self.stack.len() >= 2, "can't pop last frame from the stack");
        self.stack.pop();
    }
}
