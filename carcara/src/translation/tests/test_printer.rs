//! Test suite for Eunoia AST's pretty printer.
#[cfg(test)]
use crate::translation::{eunoia_ast::*, printer::PrintProof, printer::*};

#[cfg(test)]
use rug::Integer;

#[cfg(test)]
use rug::Rational;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        let assumes = vec![
            // Atomic type constructors
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Type(EunoiaType::Bool),
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Type(EunoiaType::Type),
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Type(EunoiaType::Real),
            },
            // An already declared Sort.
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Type(EunoiaType::Name(String::from("some_symbol"))),
            },
            // A (possible polymorphic) function type
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Type(EunoiaType::Fun(
                    vec![EunoiaKindParam::KindParam(
                        EunoiaType::Type,
                        vec![
                            EunoiaTypeAttr::Var(String::from("s")),
                            EunoiaTypeAttr::Implicit,
                            EunoiaTypeAttr::Requires(EunoiaTerm::False, EunoiaTerm::False),
                        ],
                    )],
                    vec![EunoiaType::Bool],
                    Box::new(EunoiaType::Bool),
                )),
            },
        ];

        let expected = "(assume a Bool)\n\
                        (assume a Type)\n\
                        (assume a Real)\n\
                        (assume a some_symbol)\n\
                        (assume a (-> (! Type :var s :implicit :requires \
                        (false false)) Bool Bool))\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_terms() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        let assumes = vec![
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Numeral(Integer::from(1)),
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Decimal(Rational::from(5)),
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Rational(Integer::from(1), Integer::from(3)),
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::String("some string".to_owned()),
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::True,
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::False,
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Id("some_symbol".to_owned()),
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::App("some_symbol".to_owned(), vec![EunoiaTerm::True]),
            },
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Op(EunoiaOperator::Xor, vec![EunoiaTerm::True]),
            },
        ];

        let expected = "(assume a 1)\n\
                        (assume a 5.0)\n\
                        (assume a 1/3)\n\
                        (assume a \"some string\")\n\
                        (assume a true)\n\
                        (assume a false)\n\
                        (assume a some_symbol)\n\
                        (assume a (some_symbol true))\n\
                        (assume a (xor true))\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_assume() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        let assumes = vec![
            EunoiaCommand::Assume {
                name: String::from("a"),
                term: EunoiaTerm::Type(EunoiaType::Bool),
            },
            EunoiaCommand::Assume {
                name: String::from("b"),
                term: EunoiaTerm::Type(EunoiaType::Type),
            },
            EunoiaCommand::Assume {
                name: String::from("c"),
                term: EunoiaTerm::Type(EunoiaType::Real),
            },
        ];

        let expected = "(assume a Bool)\n\
                        (assume b Type)\n\
                        (assume c Real)\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_assume_push() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        let assumes = vec![
            EunoiaCommand::AssumePush {
                name: String::from("a"),
                term: EunoiaTerm::Type(EunoiaType::Bool),
            },
            EunoiaCommand::AssumePush {
                name: String::from("b"),
                term: EunoiaTerm::Type(EunoiaType::Type),
            },
            EunoiaCommand::AssumePush {
                name: String::from("c"),
                term: EunoiaTerm::Type(EunoiaType::Real),
            },
        ];

        let expected = "(assume-push a Bool)\n\
                        (assume-push b Type)\n\
                        (assume-push c Real)\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_declare_const() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        // TODO: just a simple but semantically unsound test
        let assumes = vec![EunoiaCommand::DeclareConst {
            name: String::from("a"),
            eunoia_type: EunoiaTerm::Type(EunoiaType::Real),
            attrs: vec![EunoiaConsAttr::RightAssoc],
        }];

        let expected = "(declare-const a Real :right-assoc)\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_declare_type() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        // TODO: just a simple but semantically unsound test
        let assumes = vec![EunoiaCommand::DeclareType {
            name: String::from("S"),
            kind: EunoiaList { list: vec![] },
        }];

        let expected = "(declare-type S ( ))\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_define() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        // TODO: just a simple but semantically unsound test
        let assumes = vec![EunoiaCommand::Define {
            name: String::from("some_variale"),
            typed_params: EunoiaList {
                list: vec![EunoiaTypedParam {
                    name: "param1".to_owned(),
                    eunoia_type: EunoiaType::Type,
                    attrs: vec![EunoiaConsAttr::RightAssoc],
                }],
            },
            term: EunoiaTerm::True,
            attrs: vec![EunoiaDefineAttr::Type(EunoiaType::Bool)],
        }];

        let expected = "(define some_variale ( (param1 Type :right-assoc) ) \
                        true :type Bool)\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_program() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        // TODO: just a simple but semantically unsound test
        let assumes = vec![EunoiaCommand::Program {
            name: String::from("to_cl"),
            typed_params: EunoiaList {
                list: vec![EunoiaTypedParam {
                    name: "T".to_owned(),
                    eunoia_type: EunoiaType::Bool,
                    attrs: vec![],
                }],
            },
            params: EunoiaList { list: vec![EunoiaType::Bool] },
            ret: EunoiaType::Bool,
            body: EunoiaList {
                list: vec![
                    (
                        EunoiaTerm::App(
                            "to_cl".to_owned(),
                            vec![EunoiaTerm::App(
                                "@cl".to_owned(),
                                vec![EunoiaTerm::Id("T".to_owned())],
                            )],
                        ),
                        EunoiaTerm::App("@cl".to_owned(), vec![EunoiaTerm::Id("T".to_owned())]),
                    ),
                    (
                        EunoiaTerm::App("to_cl".to_owned(), vec![EunoiaTerm::Id("T".to_owned())]),
                        EunoiaTerm::App("@cl".to_owned(), vec![EunoiaTerm::Id("T".to_owned())]),
                    ),
                ],
            },
        }];

        let expected = "(program to_cl ( (T Bool) ) \
                        ( Bool ) Bool \
                        ( \
                         ((to_cl (@cl T)) (@cl T)) \
                         ((to_cl T) (@cl T)) ))\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_set_logic() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        let assumes = vec![EunoiaCommand::SetLogic { name: String::from("QF_UFLRA") }];

        let expected = "(set-logic QF_UFLRA)\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_step() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        let assumes = vec![EunoiaCommand::Step {
            id: String::from("t1"),
            conclusion_clause: Some(EunoiaTerm::Id("some_conclusion".to_owned())),
            rule: "let_elim".to_owned(),
            premises: EunoiaList {
                list: vec![
                    EunoiaTerm::Id("context".to_owned()),
                    EunoiaTerm::Id("h1".to_owned()),
                    EunoiaTerm::Id("t1".to_owned()),
                ],
            },
            arguments: EunoiaList {
                list: vec![EunoiaTerm::Id("context".to_owned())],
            },
        }];

        let expected = "(step t1 some_conclusion :rule let_elim :premises ( context h1 t1 ) \
                        :args ( context ))\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    #[test]
    fn test_step_pop() {
        let mut buf = Vec::new();
        let s_exp_formatter = SExpFormatter::new(&mut buf);

        let mut printer = EunoiaPrinter::new(s_exp_formatter);

        let assumes = vec![EunoiaCommand::StepPop {
            id: String::from("t1"),
            conclusion_clause: Some(EunoiaTerm::Id("some_conclusion".to_owned())),
            rule: "let_elim".to_owned(),
            premises: EunoiaList {
                list: vec![
                    EunoiaTerm::Id("context".to_owned()),
                    EunoiaTerm::Id("h1".to_owned()),
                    EunoiaTerm::Id("t1".to_owned()),
                ],
            },
            arguments: EunoiaList {
                list: vec![EunoiaTerm::Id("context".to_owned())],
            },
        }];

        let expected = "(step-pop t1 some_conclusion :rule let_elim :premises ( context h1 t1 ) \
                        :args ( context ))\n";

        printer.write_proof(&assumes).unwrap();
        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }
}
