/// Translator trait for `EunoiaProof`
use rug::Integer; // TODO: why are we using rug?

use super::Translator;
use crate::ast::*;
use crate::translation::alethe_signature::theory::*;
use crate::translation::eunoia_ast::*;

use indexmap::IndexSet;

pub struct EunoiaTranslator;

impl EunoiaTranslator {
    // NOTE: it is pub for testing purposes
    pub fn translate(&mut self, proof: &Rc<ProofNode>) -> EunoiaProof {
        let command_list = proof.into_commands();
        EunoiaTranslator::translate_commands(&command_list)
    }

    fn translate_commands(command_list: &[ProofCommand]) -> EunoiaProof {
        // TODO: see for a better way of including Alethe's signature
        // We are not including it into the Pool of terms
        let alethe_signature = AletheTheory::new();

        let mut eunoia_proof = Vec::new();

        // To get a ProofIter object
        let proof = Proof {
            premises: IndexSet::new(),
            constant_definitions: Vec::new(),
            // TODO: ugly?
            commands: command_list.to_vec(),
        };
        // ProofIter objects to get commands indexed by pairs
        let proof_iter = proof.iter();
        let mut command_list_iter = proof.commands.iter();
        let mut some_command;

        // TODO: simple fix to deal with contexts
        // TODO: is it possible to define a private name-space prefixing some
        // symbol?
        // (define ctx0 () true)
        let mut contexts_opened = 0; // Counter for contexts opened
        let mut context_name = String::from("ctx") + &contexts_opened.to_string();
        eunoia_proof.push(EunoiaCommand::Define {
            name: context_name.clone(), // TODO: performance?
            typed_params: Vec::new(),
            term: EunoiaTerm::True,
            attrs: Vec::new(),
        });

        // (assume context ctx0)
        eunoia_proof.push(EunoiaCommand::Assume {
            name: String::from("context"),
            term: EunoiaTerm::Id(context_name.clone()),
        });

        contexts_opened += 1;

        loop {
            some_command = command_list_iter.next();

            match some_command {
                Some(command) => {
                    match command {
                        ProofCommand::Assume { id, term } => {
                            eunoia_proof.push(
                                // TODO: what about :named?
                                EunoiaCommand::Assume {
                                    name: id.clone(),
                                    term: EunoiaTranslator::translate_term(term),
                                },
                            );
                        }

                        ProofCommand::Step(ProofStep {
                            id, clause, rule, premises, args, ..
                        }) => {
                            let alethe_premises: Vec<Symbol> = premises
                                .iter()
                                .map(|pair| String::from(proof_iter.get_premise(*pair).id()))
                                .collect();

                            // NOTE: in ProofStep, clause has type
                            // Vec<Rc<Term>>, though it represents an
                            // invocation of Alethe's cl operator
                            let conclusion: EunoiaTerm = EunoiaTerm::List(
                                alethe_signature.get_cl_symbol(),
                                clause
                                    .iter()
                                    .map(|term| EunoiaTranslator::translate_term(term))
                                    .collect(),
                            );
                            // NOTE: not adding conclusion clause to this list
                            let eunoia_arguments: Vec<EunoiaTerm> = args
                                .iter()
                                .map(EunoiaTranslator::translate_proof_arg)
                                .collect();

                            eunoia_proof.push(EunoiaCommand::Step {
                                name: id.clone(),
                                conclusion_clause: conclusion,
                                rule: rule.clone(),
                                premises: alethe_premises,
                                arguments: eunoia_arguments,
                            });
                        }

                        // A subproof introduced by the 'anchor' command
                        ProofCommand::Subproof(Subproof { commands, args, .. }) => {
                            // Define and open a new context
                            // (define ctx1 () (@ctx ((x S)) (and (= x b) ctx0)))
                            // (assume-push context ctx1)
                            context_name = String::from("ctx") + &contexts_opened.to_string();
                            // To store parameters to @ctx
                            // TODO: should be a list of EunoiaTypedParam
                            let mut ctx_params = Vec::new();
                            // To store the application of 'and'
                            let mut and_app: Vec<EunoiaTerm> = Vec::new();
                            // TODO: this should be an EunoiaTerm::List
                            and_app.push(EunoiaTerm::Id(String::from("and")));

                            args.iter().for_each(|arg| match arg {
                                AnchorArg::Variable((name, sort)) => {
                                    ctx_params.push(EunoiaTerm::Var(
                                        name.clone(),
                                        Box::new(EunoiaTranslator::translate_term(sort)),
                                    ));
                                }
                                AnchorArg::Assign((name, _sort), term) => {
                                    and_app.push(EunoiaTerm::Op(
                                        EunoiaOperator::Eq,
                                        vec![
                                            EunoiaTerm::Id(name.clone()),
                                            EunoiaTranslator::translate_term(term),
                                        ],
                                    ));
                                }
                            });

                            // Concat (and...)
                            ctx_params.append(&mut and_app);

                            eunoia_proof.push(EunoiaCommand::Define {
                                name: context_name.clone(),
                                typed_params: Vec::new(),
                                // TODO: define @ctx in theory.rs
                                term: EunoiaTerm::List(String::from("@ctx"), ctx_params),
                                attrs: Vec::new(),
                            });

                            // (assume context ctx0)
                            eunoia_proof.push(EunoiaCommand::AssumePush {
                                name: String::from("context"),
                                term: EunoiaTerm::Id(context_name.clone()),
                            });

                            // New context opened.
                            contexts_opened += 1;

                            // Continue with the remaining commands
                            EunoiaTranslator::translate_commands(commands);
                        }
                    }
                }

                None => {
                    break;
                }
            }
        }

        eunoia_proof
    }

    fn translate_term(term: &Term) -> EunoiaTerm {
        match term {
            Term::Const(constant) => EunoiaTranslator::translate_constant(constant),

            Term::Sort(sort) => EunoiaTerm::Type(EunoiaTranslator::translate_sort(sort)),

            Term::Op(operator, operands) => {
                let operands_eunoia = operands
                    .iter()
                    .map(|operand| EunoiaTranslator::translate_term(operand))
                    .collect();

                EunoiaTerm::Op(
                    EunoiaTranslator::translate_operator(*operator),
                    operands_eunoia,
                )
            }

            Term::Var(string, term) => EunoiaTerm::Var(
                string.clone(),
                Box::new(EunoiaTranslator::translate_term(term)),
            ),

            _ => EunoiaTerm::True,
        }
    }

    fn translate_operator(operator: Operator) -> EunoiaOperator {
        match operator {
            // Boolean operators.
            Operator::Xor => EunoiaOperator::Xor,

            Operator::Not => EunoiaOperator::Not,

            // Order / Comparison.
            Operator::Equals => EunoiaOperator::Eq,

            Operator::GreaterThan => EunoiaOperator::GreaterThan,

            Operator::GreaterEq => EunoiaOperator::GreaterEq,

            // TODO: ?
            Operator::LessThan => EunoiaOperator::LessThan,

            Operator::LessEq => EunoiaOperator::LessEq,

            _ => EunoiaOperator::Not,
        }
    }

    fn translate_constant(constant: &Constant) -> EunoiaTerm {
        match constant {
            Constant::Integer(integer) => EunoiaTerm::Numeral(integer.clone()),

            Constant::Real(rational) => EunoiaTerm::Decimal(rational.clone()),

            _ => EunoiaTerm::True,
        }
    }

    // TODO:
    fn translate_sort(sort: &Sort) -> EunoiaType {
        match sort {
            Sort::Real => EunoiaType::Real,

            // User-defined sort
            // TODO: what about args?
            Sort::Atom(string, ..) => EunoiaType::Name(string.clone()),

            _ => {
                EunoiaType::Real
                // TODO:
            }
        }
    }

    fn translate_proof_arg(proof_arg: &ProofArg) -> EunoiaTerm {
        match proof_arg {
            // An argument that is just a term.
            ProofArg::Term(term) => EunoiaTranslator::translate_term(term),

            ProofArg::Assign(.., term) => {
                // TODO: how should we translate (:= <symbol> <term>)?
                EunoiaTranslator::translate_term(term)
            }
        }
    }

    // TODO: don't know if this will be actually needed
    /// Translates only an SMT-lib problem prelude.
    pub fn translate_problem_prelude(prelude: &ProblemPrelude) -> EunoiaProof {
        let ProblemPrelude {
            sort_declarations,
            function_declarations,
            logic,
        } = prelude;

        let mut eunoia_prelude = Vec::new();

        match logic {
            Some(logic_name) => {
                eunoia_prelude.push(EunoiaCommand::SetLogic { name: logic_name.clone() });
            }

            None => {}
        }

        sort_declarations.iter().for_each(|pair| {
            eunoia_prelude.push(EunoiaCommand::DeclareSort {
                name: pair.0.clone(),
                arity: EunoiaTerm::Numeral(Integer::from(pair.1)),
            });
        });

        function_declarations.iter().for_each(|pair| {
            eunoia_prelude.push(EunoiaCommand::DeclareConst {
                name: pair.0.clone(),
                eunoia_type: EunoiaTranslator::translate_term(&pair.1),
                attrs: Vec::new(),
            });
        });

        eunoia_prelude
    }
}

impl Translator for EunoiaTranslator {
    type Output = EunoiaProof;

    fn translate(&mut self, _proof: &Rc<ProofNode>) -> Self::Output {
        self.translate(_proof)
    }
}
