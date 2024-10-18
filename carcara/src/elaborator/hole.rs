use super::*;
use crate::{checker, parser, CarcaraResult};
use std::{
    io::{self, BufRead, Write},
    process::{Command, Stdio},
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum HoleError {
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
    writeln!(&mut problem, "(set-option :produce-proofs true)").unwrap();
    write!(&mut problem, "{}", prelude).unwrap();

    let mut bytes = Vec::new();
    printer::write_lia_smt_instance(pool, prelude, &mut bytes, conclusion, false).unwrap();
    write!(&mut problem, "{}", String::from_utf8(bytes).unwrap()).unwrap();

    writeln!(&mut problem, "(check-sat)").unwrap();
    writeln!(&mut problem, "(get-proof)").unwrap();
    writeln!(&mut problem, "(exit)").unwrap();

    problem
}

pub fn hole(elaborator: &mut Elaborator, step: &StepNode) -> Option<Rc<ProofNode>> {
    let prelude = elaborator.problem.prelude.clone();
    let prelude = if prelude.logic.as_deref() == Some("QF_LIA") {
        ProblemPrelude {
            logic: Some("QF_LIRA".into()),
            ..prelude
        }
    } else {
        prelude
    };
    let problem = get_problem_string(elaborator.pool, &prelude, &step.clause);
    let options = elaborator.config.hole_options.as_ref().unwrap();
    let commands = match get_solver_proof(elaborator.pool, problem.clone(), options) {
        Ok((c, false)) => c,
        Ok((_, true)) => {
            log::warn!("failed to elaborate `all_simplify` step: solver proof contains holes");
            return None;
        }
        Err(e) => {
            log::warn!("failed to elaborate `all_simplify` step: {}", e);
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
    options: &HoleOptions,
) -> Result<(Vec<ProofCommand>, bool), HoleError> {
    let mut process = Command::new(options.solver.as_ref())
        .args(options.arguments.iter().map(AsRef::as_ref))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(HoleError::FailedSpawnSolver)?;

    process
        .stdin
        .take()
        .expect("failed to open solver stdin")
        .write_all(problem.as_bytes())
        .map_err(HoleError::FailedWriteToSolverStdin)?;

    let output = process
        .wait_with_output()
        .map_err(HoleError::FailedWaitForSolver)?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("interrupted by timeout.") {
                return Err(HoleError::SolverTimeout);
            }
        }
        return Err(HoleError::NonZeroExitCode(output.status.code()));
    }

    let mut proof = output.stdout.as_slice();
    let mut first_line = String::new();

    proof
        .read_line(&mut first_line)
        .map_err(|_| HoleError::SolverGaveInvalidOutput)?;

    if first_line.trim_end() != "unsat" {
        return Err(HoleError::OutputNotUnsat);
    }

    parse_and_check_solver_proof(pool, problem.as_bytes(), proof)
        .map_err(|e| HoleError::InnerProofError(Box::new(e)))
}

fn parse_and_check_solver_proof(
    pool: &mut PrimitivePool,
    problem: &[u8],
    proof: &[u8],
) -> CarcaraResult<(Vec<ProofCommand>, bool)> {
    let config = parser::Config {
        apply_function_defs: false,
        expand_lets: true,
        allow_int_real_subtyping: true,
        strict: false,
        parse_hole_args: false,
    };

    let (problem, proof) = parser::parse_instance_with_pool(problem, proof, config, pool)?;

    let config = checker::Config::new();
    let res = checker::ProofChecker::new(pool, config).check(&problem, &proof)?;
    Ok((proof.commands, res))
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

    let mut clause: Vec<_> = conclusion
        .iter()
        .map(|l| build_term!(pool, (not (not {l.clone()}))))
        .collect();

    clause.push(pool.bool_false());

    let proof = increase_subproof_depth(&proof, depth + 1, root_id);
    let subproof_assumptions = proof.get_assumptions_of_depth(depth + 1);

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
