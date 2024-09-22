use rug::Integer; // TODO: why are we using this?
use rug::Rational; // TODO: why are we using this?

use crate::translation::eunoia_ast::*;
use crate::translation::eunoia::*;
use crate::{
    ast::*,
    parser::tests::*,
};

// TODO: ugly, copying this from parser/tests.rs
use crate::parser::*;
const ERROR_MESSAGE: &str = "parser error during test";
const TEST_CONFIG: Config = Config {
    // Some tests need function definitions to be applied
    apply_function_defs: true,
    expand_lets: false,
    allow_int_real_subtyping: false,
    strict: false,
};

#[test]
fn test_small_example() {
    let mut eunoia_translator = EunoiaTranslator{};

    let problem_prelude = "(set-logic QF_UFLRA)
                   (declare-const a Real)
                   (declare-const b Real)

                   (assert (xor (not (> a 5.0)) (= b 10.0)))
                   (assert (not (= b 10.0)))
                   (assert (not (<= a 5.0)))";

    // TODO: in (! (= b 10.0) :named s1), s1 seems to be considered
    // an identifier introduced during parsing, and each of its
    // occurrences are replaced, later, by = b 10.0
    // TODO: ProofNode::from_commands(proof_ast.commands);
    // returns only the last command
    let mut alethe_certificate = "(assume h1 (xor (not (> a 5.0)) (! (= b 10.0) :named s1)))
                          (assume h2 (not (= b 10.0)))
                          (assume h3 (not (<= a 5.0)))

                          (step t1 (cl (not (> a 5.0)) s1) :rule xor1 :premises (h1))
                          (step t2 (cl (<= a 5.0) (> a 5.0)) :rule la_generic :args (1.0 1.0))
                          (step t3 (cl) :rule resolution :premises (t1 t2 h2 h3))";
    // TODO: in small.eo step t2 is translated as:
    // (step t2 :rule la_generic :args ((@cl (<= a 5.0) (> a 5.0)) (+ 1.0 1.0)))
    // note the list of arguments: why the '+'?
    // TODO: ugly, copying this from parser/tests.rs
    let (mut prelude_ast, mut proof_ast, mut pool) = parse_instance(problem_prelude.as_bytes(), 
                                                        alethe_certificate.as_bytes(),
                                                        TEST_CONFIG)
        .expect(ERROR_MESSAGE);

    let eunoia_prelude = EunoiaTranslator::translate_problem_prelude(&prelude_ast);
    let mut commands = ProofNode::from_commands(proof_ast.commands);
    let mut eunoia_proof = eunoia_translator.translate(&commands);
    let command_list = commands.into_commands();
    
    assert_eq!(eunoia_prelude, 
               vec![EunoiaCommand::DeclareConst{name : String::from("a"),
                                                eunoia_type: EunoiaTerm::Type(
                                                    EunoiaType::Real),
                                                attrs : Vec::new()},
                    EunoiaCommand::DeclareConst{name : String::from("b"),
                                                eunoia_type: EunoiaTerm::Type(
                                                    EunoiaType::Real),
                                                attrs : Vec::new()}]);

    // TODO: the returned command list does not contain commands in the
    // expected order.
    assert_eq!(command_list, Vec::new());

    let gt = EunoiaTerm::Op(
        EunoiaOperator::GreaterThan,
        vec![EunoiaTerm::Var(String::from("a"),            
                             Box::new(EunoiaTerm::Type(EunoiaType::Real))), 
             EunoiaTerm::Decimal(Rational::from(5))]);

    let s1 = EunoiaTerm::Op(
        EunoiaOperator::Eq, 
        vec![EunoiaTerm::Var(String::from("b"), 
                             Box::new(EunoiaTerm::Type(EunoiaType::Real))), 
             EunoiaTerm::Decimal(Rational::from(10))]);

    let not_le = EunoiaTerm::Op(
        EunoiaOperator::LessEq, 
        vec![EunoiaTerm::Var(String::from("a"), 
                             Box::new(EunoiaTerm::Type(EunoiaType::Real))), 
             EunoiaTerm::Decimal(Rational::from(5))]);

    assert_eq!(eunoia_proof, 
               vec![EunoiaCommand::Assume {
                   name: String::from("h1"), 
                   term: EunoiaTerm::Op(
                       EunoiaOperator::Xor, 
                       vec![EunoiaTerm::Op(EunoiaOperator::Not, 
                                           vec![gt.clone()]), 
                            s1.clone()])},
                    EunoiaCommand::Assume { 
                        name: String::from("h2"), 
                        term: 
                        EunoiaTerm::Op(EunoiaOperator::Not, 
                                       vec![s1.clone()])},
                    EunoiaCommand::Assume { 
                        name: String::from("h3"), 
                        term: EunoiaTerm::Op(EunoiaOperator::Not, 
                                             vec![not_le.clone()])}
               ]);
}
