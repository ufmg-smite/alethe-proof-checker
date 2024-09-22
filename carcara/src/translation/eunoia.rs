/// Translator trait for EunoiaProof
use super::Translator;
use crate::ast::*;
use crate::translation::eunoia_ast::*;
use crate::translation::alethe_signature::theory::*;

use indexmap::IndexSet;

pub struct EunoiaTranslator;

impl EunoiaTranslator {
    // NOTE: it is pub for testing purposes
    pub fn translate(&mut self, _proof: &Rc<ProofNode>) -> EunoiaProof {
        // TODO: see for a better way of including Alethe's signature
        // We are not including it into the Pool of terms
        let alethe_signature = AletheTheory::new();

        let mut eunoia_proof = Vec::new();

        let command_list = _proof.into_commands();
        // To get a ProofIter object
        let proof = Proof {premises: IndexSet::new(),
                           constant_definitions: Vec::new(),
                           commands: command_list};
        // ProofIter objects to get commands indexed by pairs
        let proof_iter = proof.iter();
        let mut command_list_iter = proof.commands.iter();
        let mut some_command;

        loop {
            some_command = command_list_iter.next();

            match some_command {
                Some(command) => {
                    match command {
                        ProofCommand::Assume{id, term} => {
                            eunoia_proof.push(
                                // TODO: what about :named?
                                EunoiaCommand::Assume{name : id.clone(), 
                                                      term : EunoiaTranslator::translate_term(term),
                                }
                            )
                        },
                        
                        ProofCommand::Step(proofstep) => {
                            match proofstep {
                                ProofStep {id, clause, rule, premises, args, 
                                           discharge} => {
                                    let alethe_premises : Vec<Symbol> = 
                                        premises
                                        .into_iter()
                                        .map(|pair| 
                                             String::from(
                                                 proof_iter
                                                     .get_premise(*pair)
                                                     .id())).collect();

                                    // NOTE: in ProofStep, clause has type
                                    // Vec<Rc<Term>>, though it represents an
                                    // invocation of Alethe's cl operator
                                    let conclusion : EunoiaTerm = 
                                        EunoiaTerm::List(
                                            alethe_signature.get_cl_symbol(),
                                            clause
                                                .into_iter()
                                                .map(|term| 
                                                     EunoiaTranslator::translate_term(term)).collect());

                                    // NOTE: not adding conclusion clause to this list
                                    let eunoia_arguments : Vec<EunoiaTerm> = 
                                        args
                                        .into_iter()
                                        .map(|arg| 
                                             EunoiaTranslator::translate_proof_arg(arg)).collect();
                                    
                                    eunoia_proof.push(
                                        EunoiaCommand::Step{
                                            name : id.clone(),
                                            conclusion_clause : conclusion,
                                            rule : rule.clone(),
                                            premises : alethe_premises,
                                            arguments : eunoia_arguments
                                        })
                                }
                            }
                        },
                        
                        ProofCommand::Subproof(subproof) => break,
                    }
                },
                    
                None => {
                    break;
                }
            }
        };
        
        return eunoia_proof;
    }

    fn translate_term(term: &Term) -> EunoiaTerm {
        match term {
            Term::Const(constant) => {
                EunoiaTranslator::translate_constant(constant)
            },

            Term::Sort(sort) => {
                EunoiaTerm::Type(EunoiaTranslator::translate_sort(sort))
            },

            Term::Op(operator, operands) => {
                let operands_eunoia = operands.into_iter().map(
                    |operand| EunoiaTranslator::translate_term(operand))
                    .collect();

                EunoiaTerm::Op(EunoiaTranslator::translate_operator(operator),
                               operands_eunoia)
            },
            
            // Term::Binder(binder, binding_list, term) => {
            //     panic!()
            // },

            // Term::Let(binding_list, term) => {
            //     panic!()
            // },

            Term::Var(string, term) => {
                EunoiaTerm::Var(string.clone(),
                                Box::new(EunoiaTranslator::translate_term(term)))
            },  

            _ => {
                EunoiaTerm::True
            }
        }
    }

    fn translate_operator(operator: &Operator) -> EunoiaOperator {
        match operator {
            // Boolean operators.
            Operator::Xor => {
                EunoiaOperator::Xor
            },
            
            Operator::Not => {
                EunoiaOperator::Not
            },
            
            // Order / Comparison.
            Operator::Equals => {
                EunoiaOperator::Eq
            },

            Operator::GreaterThan => {
                EunoiaOperator::GreaterThan
            },

            Operator::GreaterEq => {
                EunoiaOperator::GreaterEq
            },

            // TODO: ?
            Operator::LessThan => {
                EunoiaOperator::LessThan
            },

            
            Operator::LessEq => {
                EunoiaOperator::LessEq
            },

            _ => {
                EunoiaOperator::Not
            },
        }
    }

    
    fn translate_constant(constant: &Constant) -> EunoiaTerm {
        match constant {
            Constant::Integer(integer) => {
                EunoiaTerm::Numeral(integer.clone())
            },

            Constant::Real(rational) => {
                EunoiaTerm::Decimal(rational.clone())
            },

            _ => {
                EunoiaTerm::True
            }

            
            // /// A real constant term.
            // Real(Rational),

            // /// A string literal term.
            // String(String),

            // BitVec(Integer, Integer),
            
        }
    }

    fn translate_sort(sort: &Sort) -> EunoiaType {
        match sort {
            Sort::Real => {
                EunoiaType::Real
            },
            _ => {
                EunoiaType::Real
            }
        }
    }

    fn translate_proof_arg(proof_arg: &ProofArg) -> EunoiaTerm {
        match proof_arg {
            ProofArg::Term(term) => {
                EunoiaTranslator::translate_term(term)
            },

            ProofArg::Assign(string, term) => {
                EunoiaTerm::List(string.clone(), 
                                 vec![EunoiaTranslator::translate_term(term)])
            }
        }
    }
    
    // TODO: don't know if this will be actually needed
    // TODO: simplifying first step:
    // problem_prelude :
    // - declare-const:
    //   only names, no specified types
    // - no set-logic
    // - no assert
    // - no sorts
    pub fn translate_problem_prelude(prelude: &ProblemPrelude) 
                                     -> EunoiaProof {
        match prelude {
            ProblemPrelude {sort_declarations,
                            function_declarations,
                            logic} => {
                // function_declarations: Vec<(String, Rc<Term>)
                // simplification:
                // - first simple step: only extract names as strings
                // - for each string, construct a declare-const
                // - 
                // let names : Vec<String> = function_declarations.into_iter()
                //     .map(|pair| pair.0.clone()).collect();

                let consts : Vec<EunoiaCommand> = function_declarations.into_iter()
                    .map(|pair| 
                         EunoiaCommand::DeclareConst {name : pair.0.clone(),
                                                      eunoia_type: EunoiaTranslator::translate_term(&*pair.1),
                                                      attrs : Vec::new()}).collect();
                consts
            }
        }
    }
}

impl Translator for EunoiaTranslator {
    type Output = EunoiaProof;

    fn translate(&mut self, _proof: &Rc<ProofNode>) -> Self::Output {
        return self.translate(_proof);
    }
}
