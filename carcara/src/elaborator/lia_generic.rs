use super::*;
use crate::{checker, parser, CarcaraResult};
use std::{
    io::{self, BufRead, Write},
    process::{Command, Stdio},
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LiaGenericError {
    #[error("failed to spawn solver process")]
    FailedSpawnSolver(io::Error),

    #[error("failed to write to solver stdin")]
    FailedWriteToSolverStdin(io::Error),

    #[error("error while waiting for solver to exit")]
    FailedWaitForSolver(io::Error),

    #[error("solver gave invalid output")]
    SolverGaveInvalidOutput,

    #[error("solver output not unsat")]
    OutputNotUnsat,

    #[error("solver timed out when solving problem")]
    SolverTimeout,

    #[error(
        "solver returned non-zero exit code: {}",
        if let Some(i) = .0 { format!("{}", i) } else { "none".to_owned() }
    )]
    NonZeroExitCode(Option<i32>),

    #[error("error in inner proof: {0}")]
    InnerProofError(Box<crate::Error>),
}

fn get_problem_string(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    conclusion: &[Rc<Term>],
) -> String {
    use std::fmt::Write;

    let mut problem = String::new();
    write!(&mut problem, "(set-option :produce-proofs true)").unwrap();
    write!(&mut problem, "{}", prelude).unwrap();

    let mut bytes = Vec::new();
    printer::write_lia_smt_instance(pool, prelude, &mut bytes, conclusion, true).unwrap();
    write!(&mut problem, "{}", String::from_utf8(bytes).unwrap()).unwrap();

    writeln!(&mut problem, "(check-sat)").unwrap();
    writeln!(&mut problem, "(get-proof)").unwrap();
    writeln!(&mut problem, "(exit)").unwrap();

    problem
}

pub fn lia_generic(elaborator: &mut Elaborator, step: &StepNode) -> Option<Rc<ProofNode>> {
    let problem = get_problem_string(elaborator.pool, elaborator.prelude, &step.clause);
    let options = elaborator.config.lia_options.as_ref().unwrap();
    let commands = match get_solver_proof(elaborator.pool, problem, options) {
        Ok(c) => c,
        Err(e) => {
            log::warn!("failed to elaborate `lia_generic` step: {}", e);
            return None;
        }
    };

    Some(insert_solver_proof(
        elaborator.pool,
        commands,
        &step.clause,
        &step.id,
        step.depth,
    ))
}

fn get_solver_proof(
    pool: &mut PrimitivePool,
    problem: String,
    options: &LiaGenericOptions,
) -> Result<Vec<ProofCommand>, LiaGenericError> {
    let mut process = Command::new(options.solver.as_ref())
        .args(options.arguments.iter().map(AsRef::as_ref))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(LiaGenericError::FailedSpawnSolver)?;

    process
        .stdin
        .take()
        .expect("failed to open solver stdin")
        .write_all(problem.as_bytes())
        .map_err(LiaGenericError::FailedWriteToSolverStdin)?;

    let output = process
        .wait_with_output()
        .map_err(LiaGenericError::FailedWaitForSolver)?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("interrupted by timeout.") {
                return Err(LiaGenericError::SolverTimeout);
            }
        }
        return Err(LiaGenericError::NonZeroExitCode(output.status.code()));
    }

    let mut proof = output.stdout.as_slice();
    let mut first_line = String::new();

    proof
        .read_line(&mut first_line)
        .map_err(|_| LiaGenericError::SolverGaveInvalidOutput)?;

    if first_line.trim_end() != "unsat" {
        return Err(LiaGenericError::OutputNotUnsat);
    }

    parse_and_check_solver_proof(pool, problem.as_bytes(), proof)
        .map_err(|e| LiaGenericError::InnerProofError(Box::new(e)))
}

fn parse_and_check_solver_proof(
    pool: &mut PrimitivePool,
    problem: &[u8],
    proof: &[u8],
) -> CarcaraResult<Vec<ProofCommand>> {
    let config = parser::Config {
        apply_function_defs: false,
        expand_lets: true,
        allow_int_real_subtyping: true,
        allow_unary_logical_ops: true,
    };
    let mut parser = parser::Parser::new(pool, config, problem)?;
    let (_, premises) = parser.parse_problem()?;
    parser.reset(proof)?;
    let commands = parser.parse_proof()?;
    let proof = Proof { premises, commands };

    let config = checker::Config::new().ignore_unknown_rules(true);
    checker::ProofChecker::new(pool, config).check(&proof)?;
    Ok(proof.commands)
}

fn get_subproof_assumptions(
    pool: &mut PrimitivePool,
    conclusion: &[Rc<Term>],
    proof: &Rc<ProofNode>,
    root_id: &str,
    root_depth: usize,
) -> Vec<Rc<ProofNode>> {
    let assumptions = proof.get_assumptions();
    let assume_term_to_node: HashMap<&Rc<Term>, Rc<ProofNode>> = assumptions
        .iter()
        .map(|node| {
            let (_, _, term) = node.as_assume().unwrap();
            (term, node.clone())
        })
        .collect();

    // This is a bit ugly, but we have to add the ".added" to avoid colliding with the first few
    // steps in the solver proof
    let mut ids = IdHelper::new(&format!("{}.added", root_id));
    conclusion
        .iter()
        .map(|term| {
            let term = build_term!(pool, (not {term.clone()}));
            match assume_term_to_node.get(&term) {
                Some(assume) => assume.clone(),
                None => Rc::new(ProofNode::Assume {
                    id: ids.next_id(),
                    depth: root_depth + 1,
                    term,
                }),
            }
        })
        .collect()
}

fn increase_subproof_depth(proof: &Rc<ProofNode>, delta: usize, prefix: &str) -> Rc<ProofNode> {
    mutate(proof, |_, node| {
        let node = match node.as_ref().clone() {
            ProofNode::Assume { id, depth, term } => ProofNode::Assume {
                id: format!("{}.{}", prefix, id),
                depth: depth + delta,
                term,
            },
            ProofNode::Step(mut s) => {
                s.id = format!("{}.{}", prefix, s.id);
                s.depth += delta;
                ProofNode::Step(s)
            }
            ProofNode::Subproof(_) => unreachable!(),
        };
        Rc::new(node)
    })
}

fn insert_solver_proof(
    pool: &mut PrimitivePool,
    commands: Vec<ProofCommand>,
    conclusion: &[Rc<Term>],
    root_id: &str,
    depth: usize,
) -> Rc<ProofNode> {
    let proof = ProofNode::from_commands(commands);

    let mut ids = IdHelper::new(root_id);
    let subproof_id = ids.next_id();

    let subproof_assumptions =
        get_subproof_assumptions(pool, conclusion, &proof, &subproof_id, depth);

    let mut clause: Vec<_> = subproof_assumptions
        .iter()
        .map(|node| build_term!(pool, (not {node.clause()[0].clone()})))
        .collect();

    clause.push(pool.bool_false());

    let proof = increase_subproof_depth(&proof, depth + 1, root_id);

    let last_step = Rc::new(ProofNode::Step(StepNode {
        id: subproof_id,
        depth: depth + 1,
        clause: clause.clone(),
        rule: "subproof".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: subproof_assumptions,
        previous_step: Some(proof),
    }));

    let subproof = Rc::new(ProofNode::Subproof(SubproofNode {
        last_step,
        args: Vec::new(),
        // Since the subproof was inserted from the solver proof, it cannot reference anything
        // outside of it.
        outbound_premises: Vec::new(),
    }));

    let not_not_steps: Vec<_> = clause[..clause.len() - 1]
        .iter()
        .map(|term| {
            let clause = vec![
                build_term!(pool, (not {term.clone()})),
                term.remove_negation()
                    .unwrap()
                    .remove_negation()
                    .unwrap()
                    .clone(),
            ];
            Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth,
                clause,
                rule: "not_not".to_owned(),
                ..Default::default()
            }))
        })
        .collect();

    let false_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: vec![build_term!(pool, (not {pool.bool_false()}))],
        rule: "false".to_owned(),
        ..Default::default()
    }));

    let mut premises = vec![subproof];
    premises.extend(not_not_steps);
    premises.push(false_step);

    Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: conclusion.to_vec(),
        rule: "resolution".to_owned(),
        premises,
        ..Default::default()
    }))
}