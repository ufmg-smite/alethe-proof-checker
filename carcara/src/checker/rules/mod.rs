use super::{
    error::{CheckerError, EqualityError},
    ContextStack,
};
use crate::{
    ast::*,
    utils::{Range, TypeName},
};
use std::time::Duration;

pub type RuleResult = Result<(), CheckerError>;

pub type Rule = fn(RuleArgs) -> RuleResult;

pub struct RuleArgs<'a> {
    pub(super) conclusion: &'a [Rc<Term>],
    pub(super) premises: &'a [Premise<'a>],
    pub(super) args: &'a [ProofArg],
    pub(super) pool: &'a mut dyn TermPool,
    pub(super) context: &'a mut ContextStack,

    // For rules that end a subproof, we need to pass the previous command in the subproof that it
    // is closing, because it may be implicitly referenced, and it is not given as premises. If a
    // rule is not ending a subproof, this should be `None`.
    pub(super) previous_command: Option<Premise<'a>>,
    pub(super) discharge: &'a [&'a ProofCommand],

    pub(super) polyeq_time: &'a mut Duration,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Premise<'a> {
    pub id: &'a str,
    pub clause: &'a [Rc<Term>],
    pub index: (usize, usize),
}

impl<'a> Premise<'a> {
    pub fn new(index: (usize, usize), command: &'a ProofCommand) -> Self {
        Self {
            id: command.id(),
            clause: command.clause(),
            index,
        }
    }
}

/// Helper function to get a single term from a premise, or return a
/// `CheckerError::WrongLengthOfPremiseClause` error if it doesn't succeed.
fn get_premise_term<'a>(premise: &Premise<'a>) -> Result<&'a Rc<Term>, CheckerError> {
    match premise.clause {
        [t] => Ok(t),
        cl => Err(CheckerError::WrongLengthOfPremiseClause(
            premise.id.to_owned(),
            1.into(),
            cl.len(),
        )),
    }
}

/// Asserts that the first argument is true, and returns the error specified by the second argument
/// otherwise.
macro_rules! rassert {
    ($arg:expr, $err:expr $(,)?) => {
        match $arg {
            true => Ok(()),
            false => Err($err),
        }?
    };
}

fn assert_num_premises<T: Into<Range>>(premises: &[Premise], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(premises.len()) {
        return Err(CheckerError::WrongNumberOfPremises(range, premises.len()));
    }
    Ok(())
}

fn assert_clause_len<T: Into<Range>>(clause: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(clause.len()) {
        return Err(CheckerError::WrongLengthOfClause(range, clause.len()));
    }
    Ok(())
}

fn assert_num_args<T: Into<Range>>(args: &[ProofArg], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(args.len()) {
        return Err(CheckerError::WrongNumberOfArgs(range, args.len()));
    }
    Ok(())
}

fn assert_operation_len<T: Into<Range>>(op: Operator, args: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(args.len()) {
        return Err(CheckerError::WrongNumberOfTermsInOp(op, range, args.len()));
    }
    Ok(())
}

fn assert_eq<T>(a: &T, b: &T) -> RuleResult
where
    T: Eq + Clone + TypeName,
    EqualityError<T>: Into<CheckerError>,
{
    if a != b {
        return Err(EqualityError::ExpectedEqual(a.clone(), b.clone()).into());
    }
    Ok(())
}

fn assert_is_expected<T>(got: &T, expected: T) -> RuleResult
where
    T: Eq + Clone + TypeName,
    EqualityError<T>: Into<CheckerError>,
{
    if *got != expected {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_polyeq(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> Result<(), CheckerError> {
    if !polyeq(a, b, time) {
        return Err(EqualityError::ExpectedEqual(a.clone(), b.clone()).into());
    }
    Ok(())
}

fn assert_polyeq_expected(got: &Rc<Term>, expected: Rc<Term>, time: &mut Duration) -> RuleResult {
    if !polyeq(got, &expected, time) {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_alpha_equiv_expected(
    got: &Rc<Term>,
    expected: Rc<Term>,
    time: &mut Duration,
) -> RuleResult {
    if !alpha_equiv(got, &expected, time) {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_is_bool_constant(got: &Rc<Term>, expected: bool) -> RuleResult {
    if !got.is_bool_constant(expected) {
        return Err(CheckerError::ExpectedBoolConstant(expected, got.clone()));
    }
    Ok(())
}

#[cfg(test)]
fn run_tests(test_name: &str, definitions: &str, cases: &[(&str, bool)]) {
    use crate::{checker, parser};
    use std::io::Cursor;

    for (i, (proof, expected)) in cases.iter().enumerate() {
        // This parses the definitions again for every case, which is not ideal
        let (mut problem, mut proof, mut pool) = parser::parse_instance(
            Cursor::new(definitions),
            Cursor::new(proof),
            parser::Config::new(),
        )
        .unwrap_or_else(|e| panic!("parser error during test \"{}\": {}", test_name, e));

        // Since rule tests often use `assume` commands to introduce premises, we search the proof
        // for all `assume`d terms and retroactively add them as the problem premises, to avoid
        // checker errors on the `assume`s
        problem.premises = proof
            .commands
            .iter()
            .filter_map(|c| match c {
                ProofCommand::Assume { term, .. } => Some(term.clone()),
                _ => None,
            })
            .collect();

        // All proofs must eventually reach the empty clause, so to avoid having to add a dummy
        // `(step end (cl) :rule hole)` to every rule test, we add this dummy step here
        proof.commands.push(ProofCommand::Step(ProofStep {
            id: "end".into(),
            clause: Vec::new(),
            rule: "hole".into(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        }));

        let mut checker = checker::ProofChecker::new(&mut pool, checker::Config::new());
        let got = checker.check(&problem, &proof).is_ok();
        assert_eq!(
            *expected, got,
            "test case \"{}\" index {} failed",
            test_name, i
        );
    }
}

#[cfg(test)]
macro_rules! test_cases {
    (
        definitions = $defs:expr,
        $($name:literal { $($proof:literal: $exp:literal,)* } )*
    ) => {{
        let definitions: &str = $defs;
        $({
            let name: &str = $name;
            let cases = [ $(($proof, $exp),)* ];
            $crate::checker::rules::run_tests(name, definitions, &cases);
        })*
    }};
}

// Since the rule submodules use the `test_cases` macro, we have to declare them here, after the
// macro is declared
pub(super) mod bitvectors;
pub(super) mod clausification;
pub(super) mod congruence;
pub(super) mod extras;
pub(super) mod linear_arithmetic;
pub(super) mod quantifier;
pub(super) mod reflexivity;
pub(super) mod resolution;
pub(super) mod simplification;
pub(super) mod strings;
pub(super) mod subproof;
pub(super) mod tautology;
pub(super) mod transitivity;
