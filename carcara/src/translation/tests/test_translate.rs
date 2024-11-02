//! Small test suite for Eunoia ASTs generation, from Alethe proof certificates.

#[cfg(test)]
use crate::ast::*;
#[cfg(test)]
use crate::translation::{eunoia::*, printer::PrintProof, printer::*};

// TODO: ugly, copying this from parser/tests.rs
#[cfg(test)]
use crate::parser::*;
#[cfg(test)]
const ERROR_MESSAGE: &str = "parser error during test";
#[cfg(test)]
const TEST_CONFIG: Config = Config {
    // Some tests need function definitions to be applied
    apply_function_defs: true,
    expand_lets: false,
    allow_int_real_subtyping: false,
    strict: false,
};

#[test]
fn test_small_example() {
    let mut eunoia_translator = EunoiaTranslator::new();

    let mut buf_prelude = Vec::new();
    let s_exp_formatter_prelude = SExpFormatter::new(&mut buf_prelude);
    let mut printer_prelude = EunoiaPrinter::new(s_exp_formatter_prelude);

    let mut buf_proof = Vec::new();
    let s_exp_formatter_proof = SExpFormatter::new(&mut buf_proof);
    let mut printer_proof = EunoiaPrinter::new(s_exp_formatter_proof);

    let problem_prelude = "(declare-const a Real)
                   (declare-const b Real)
                   (assert (xor (not (> a 5.0)) (= b 10.0)))
                   (assert (not (= b 10.0)))
                   (assert (not (<= a 5.0)))";

    // TODO: in (! (= b 10.0) :named s1), s1 seems to be considered
    // an identifier introduced during parsing, and each of its
    // occurrences are replaced, later, by = b 10.0
    // TODO: ProofNode::from_commands(proof_ast.commands);
    // returns only the last command
    let alethe_certificate = "(assume h1 (xor (not (> a 5.0)) (! (= b 10.0) :named s1)))
                          (assume h2 (not (= b 10.0)))
                          (assume h3 (not (<= a 5.0)))

                          (step t1 (cl (not (> a 5.0)) s1) :rule xor1 :premises (h1))
                          (step t2 (cl (<= a 5.0) (> a 5.0)) :rule la_generic :args (1.0 1.0))
                          (step t3 (cl) :rule resolution :premises (t1 t2 h2 h3))";
    // TODO: in small.eo step t2 is translated as:
    // (step t2 :rule la_generic :args ((@cl (<= a 5.0) (> a 5.0)) (+ 1.0 1.0)))
    // note the list of arguments: why the '+'?
    // TODO: ugly, copying this from parser/tests.rs
    let (prelude_ast, proof_ast, _pool) = parse_instance(
        problem_prelude.as_bytes(),
        alethe_certificate.as_bytes(),
        TEST_CONFIG,
    )
    .expect(ERROR_MESSAGE);

    let eunoia_prelude = eunoia_translator.translate_problem_prelude(&prelude_ast);

    printer_prelude.write_proof(&eunoia_prelude).unwrap();

    assert_eq!(
        "(declare-const a Real)\n\
         (declare-const b Real)\n",
        std::str::from_utf8(&buf_prelude).unwrap()
    );

    let commands = ProofNode::from_commands(proof_ast.commands);
    let eunoia_proof = eunoia_translator.translate(&commands);

    printer_proof.write_proof(eunoia_proof).unwrap();

    // TODO: fix differences with small.eo
    // TODO: maybe we do not need to have a context created if we do not
    // have an anchor statement previously
    assert_eq!(
        "(define ctx0 ( ) true)\n\
         (assume context ctx0)\n\
         (assume h1 (xor (not (> a 5.0)) (= b 10.0)))\n\
         (step t1 (@cl (not (> a 5.0)) (= b 10.0)) :rule xor1 :premises ( h1 ))\n\
         (step t2 (@cl (<= a 5.0) (> a 5.0)) :rule la_generic :args ( 1.0 1.0 ))\n\
         (assume h2 (not (= b 10.0)))\n\
         (assume h3 (not (<= a 5.0)))\n\
         (step t3 @empty_cl :rule resolution :premises ( t1 t2 h2 h3 ))\n",
        std::str::from_utf8(&buf_proof).unwrap()
    );
}

#[test]
fn test_let_example() {
    let mut eunoia_translator = EunoiaTranslator::new();

    let mut buf_prelude = Vec::new();
    let s_exp_formatter_prelude = SExpFormatter::new(&mut buf_prelude);
    let mut printer_prelude = EunoiaPrinter::new(s_exp_formatter_prelude);

    let mut buf_proof = Vec::new();
    let s_exp_formatter_proof = SExpFormatter::new(&mut buf_proof);
    let mut printer_proof = EunoiaPrinter::new(s_exp_formatter_proof);

    let problem_prelude = "(set-logic UF)
                           (declare-sort S 0)
                           (declare-const a S)
                           (declare-const b S)
                           (assert (= a b))";

    let alethe_certificate = "(assume h1 (= a b))
                              (anchor :step t2 :args ((:= x b)))
                              (step t1 (cl (= x b)) :rule refl)
                              (step t2 (cl (= (let ((x a)) x) b)) :rule let :premises (h1))";

    let (prelude_ast, proof_ast, _pool) = parse_instance(
        problem_prelude.as_bytes(),
        alethe_certificate.as_bytes(),
        TEST_CONFIG,
    )
    .expect(ERROR_MESSAGE);

    let eunoia_prelude = eunoia_translator.translate_problem_prelude(&prelude_ast);

    printer_prelude.write_proof(&eunoia_prelude).unwrap();

    assert_eq!(
        "(declare-type S ( ))\n\
         (declare-const a S)\n\
         (declare-const b S)\n",
        std::str::from_utf8(&buf_prelude).unwrap()
    );

    let commands = ProofNode::from_commands(proof_ast.commands);
    let eunoia_proof = eunoia_translator.translate(&commands);

    printer_proof.write_proof(eunoia_proof).unwrap();

    assert_eq!(
        "(define ctx0 ( ) true)\n\
         (assume context ctx0)\n\
         (assume h1 (= a b))\n\
         (define ctx1 ( ) (@ctx ( ( x S ) ) (and (= x b) ctx0)))\n\
         (assume-push context ctx1)\n\
         (step t1 (@cl (= (@var ( ( x S ) ) x) b)) \
         :rule refl :args ( context (@var ( ( x S ) ) x) b ))\n\
         (step-pop t2 (@cl (= (@let ( ( x S ) ) (@var ( ( x S ) ) x)) b)) \
         :rule let_elim :premises ( t1 ) \
         :args ( context (@let ( ( x S ) ) (@var ( ( x S ) ) x)) b ))\n",
        std::str::from_utf8(&buf_proof).unwrap()
    );
}
