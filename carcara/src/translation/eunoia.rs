//! Translator for `EunoiaProof`.

use super::Translator;
use crate::ast::*;
use crate::translation::alethe_signature::theory::*;
use crate::translation::eunoia_ast::*;

use indexmap::IndexSet;
use std::collections::HashMap;

pub struct EunoiaTranslator {
    /// Actual EunoiaProof object containing the translation.
    eunoia_proof: EunoiaProof,

    // TODO: see for a better way of including Alethe's signature
    // We are not including it into the Pool of terms
    /// "Alethe in Eunoia" signature considered during translation.
    alethe_signature: AletheTheory,

    /// Maintains contextual premises that must be included as
    /// premises in each step being translated. Typically they refer
    /// to the actual "context" computed form the set of variables and
    /// mappings defined through Alethe 'anchor' statements.
    // TODO: would it be useful to use an IndexSet?, and to use borrows?
    contextual_premises: Vec<EunoiaTerm>,

    /// Mapping variable -> sort for variables in scope, as introduced by
    /// Alethe's 'anchor' command.
    // TODO: would it be useful to use borrows?
    variables_in_scope: HashMap<String, EunoiaTerm>,
}

impl EunoiaTranslator {
    pub fn new() -> Self {
        Self {
            eunoia_proof: vec![],
            alethe_signature: AletheTheory::new(),
            contextual_premises: Vec::new(),
            variables_in_scope: HashMap::new(),
        }
    }

    pub fn translate<'a>(&'a mut self, proof: &Rc<ProofNode>) -> &'a EunoiaProof {
        let command_list = proof.into_commands();

        self.translate_commands(&command_list);

        &self.eunoia_proof
    }

    fn translate_commands(&mut self, command_list: &[ProofCommand]) {
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

        // TODO: Subproof has a context_id that could be used instead of contexts_opened
        // TODO: is it possible to define a private name-space prefixing some
        // symbol?
        // Counter for contexts opened
        let mut contexts_opened = 0;
        // TODO: do not hard-code this string constants
        let mut context_name = String::from("ctx") + &contexts_opened.to_string();

        loop {
            some_command = command_list_iter.next();

            match some_command {
                Some(command) => {
                    match command {
                        ProofCommand::Assume { id, term } => {
                            self.eunoia_proof.push(
                                // TODO: what about :named?
                                EunoiaCommand::Assume {
                                    name: id.clone(),
                                    term: self.translate_term(term),
                                },
                            );
                        }

                        ProofCommand::Step(ProofStep {
                            id, clause, rule, premises, args, ..
                        }) => {
                            self.translate_step(id, clause, rule, premises, args, &proof_iter);
                        }

                        // A subproof introduced by the 'anchor' command.
                        ProofCommand::Subproof(Subproof { commands, args, .. }) => {
                            // To store @VarList parameters to @ctx
                            let mut ctx_params = Vec::new();
                            let mut ctx_typed_params = Vec::new();
                            // To store actual parameters of 'and'
                            let mut and_params: Vec<EunoiaTerm> = Vec::new();

                            args.iter().for_each(|arg| match arg {
                                AnchorArg::Variable((name, sort)) => {
                                    // TODO: either use borrows or implement
                                    // Copy trait for EunoiaTerms
                                    // Add variables to the current scope.
                                    self.variables_in_scope
                                        .insert(name.clone(), self.translate_term(sort));

                                    // ctx_params.push(EunoiaTerm::List(
                                    //     vec![EunoiaTerm::Id(name.clone()),
                                    //          self.translate_term(sort),
                                    //     ],
                                    // ));
                                    ctx_typed_params.push(EunoiaTerm::List(vec![
                                        EunoiaTerm::Id(name.clone()),
                                        self.translate_term(sort),
                                    ]));
                                }
                                AnchorArg::Assign((name, sort), term) => {
                                    // TODO: either use borrows or implement
                                    // Copy trait for EunoiaTerms
                                    // Add variables to the current scope.
                                    self.variables_in_scope
                                        .insert(name.clone(), self.translate_term(sort));

                                    and_params.push(EunoiaTerm::App(
                                        self.alethe_signature.eq.clone(),
                                        vec![
                                            EunoiaTerm::Id(name.clone()),
                                            self.translate_term(term),
                                        ],
                                    ));

                                    ctx_typed_params.push(EunoiaTerm::List(vec![
                                        EunoiaTerm::Id(name.clone()),
                                        self.translate_term(sort),
                                    ]));
                                }
                            });

                            and_params.push(EunoiaTerm::Id(context_name.clone()));

                            // Add typed params.
                            ctx_params.push(EunoiaTerm::List(ctx_typed_params));

                            // Concat (and...)
                            ctx_params.push(EunoiaTerm::App(
                                self.alethe_signature.and.clone(),
                                and_params,
                            ));

                            if contexts_opened == 0 {
                                // (define ctx0 () true)
                                self.eunoia_proof.push(EunoiaCommand::Define {
                                    name: context_name.clone(), // TODO: performance?
                                    typed_params: EunoiaList { list: vec![] },
                                    term: EunoiaTerm::True,
                                    attrs: Vec::new(),
                                });

                                // (assume context ctx0)
                                self.eunoia_proof.push(EunoiaCommand::Assume {
                                    // TODO: do not hard-code this string
                                    name: String::from("context"),
                                    term: EunoiaTerm::Id(context_name.clone()),
                                });
                            }

                            // Add contextual premises.
                            // TODO: do not hard-code this string
                            self.contextual_premises
                                .push(EunoiaTerm::Id("context".to_owned()));

                            // Define and open a new context
                            // (define ctx1 () (@ctx ((x S)) (and (= x b) ctx0)))
                            // (assume-push context ctx1)
                            contexts_opened += 1;
                            context_name = String::from("ctx") + &contexts_opened.to_string();

                            self.eunoia_proof.push(EunoiaCommand::Define {
                                name: context_name.clone(),
                                typed_params: EunoiaList { list: Vec::new() },
                                // TODO: define @ctx in theory.rs
                                term: EunoiaTerm::App(String::from("@ctx"), ctx_params),
                                attrs: Vec::new(),
                            });

                            // (assume context ctx0)
                            self.eunoia_proof.push(EunoiaCommand::AssumePush {
                                name: String::from("context"),
                                term: EunoiaTerm::Id(context_name.clone()),
                            });

                            // New context opened.
                            contexts_opened += 1;

                            // Continue with the remaining commands
                            self.translate_commands(commands);

                            // TODO: clean contextual assumptions and var. defs.
                        }
                    }
                }

                None => {
                    break;
                }
            }
        }
    }

    fn translate_term(&self, term: &Term) -> EunoiaTerm {
        match term {
            Term::Const(constant) => EunoiaTranslator::translate_constant(constant),

            Term::Sort(sort) => EunoiaTerm::Type(EunoiaTranslator::translate_sort(sort)),

            Term::Op(operator, operands) => {
                let operands_eunoia = operands
                    .iter()
                    .map(|operand| self.translate_term(operand))
                    .collect();

                // TODO: fix this
                match operator {
                    Operator::True => EunoiaTerm::True,

                    Operator::False => EunoiaTerm::False,

                    _ => EunoiaTerm::App(
                        EunoiaTranslator::translate_operator(*operator),
                        operands_eunoia,
                    ),
                }
            }

            // TODO: not considering the sort of the variable.
            Term::Var(string, _) => {
                // Check if it is a context variable.
                if self.variables_in_scope.contains_key(string) {
                    // TODO: abstract this into a procedure
                    EunoiaTerm::App(
                        self.alethe_signature.var.clone(),
                        vec![
                            EunoiaTerm::List(vec![EunoiaTerm::List(vec![
                                EunoiaTerm::Id(string.clone()),
                                // TODO: using clone, ugly...
                                self.variables_in_scope[string].clone(),
                            ])]),
                            EunoiaTerm::Id(string.clone()),
                        ],
                    )
                } else {
                    EunoiaTerm::Id(string.clone())
                }
            }

            Term::App(fun, params) => {
                let mut fun_params = Vec::new();

                params.iter().for_each(|param| {
                    fun_params.push(self.translate_term(param));
                });

                EunoiaTerm::App((*fun).to_string(), fun_params)
            }

            Term::Let(binding_list, scope) => EunoiaTerm::App(
                self.alethe_signature.let_binder.clone(),
                vec![
                    self.translate_binding_list(binding_list),
                    self.translate_term(scope),
                ],
            ),

            _ => EunoiaTerm::True,
        }
    }

    fn translate_binding_list(&self, binding_list: &BindingList) -> EunoiaTerm {
        let mut ret = Vec::new();

        binding_list.iter().for_each(|sorted_var| {
            let (name, sort) = sorted_var;
            if self.variables_in_scope.contains_key(name) {
                // TODO: abstract this into a procedure
                ret.push(EunoiaTerm::Var(
                    name.clone(),
                    Box::new(self.variables_in_scope[name].clone()),
                ));
            } else {
                ret.push(EunoiaTerm::Var(
                    name.clone(),
                    Box::new(self.translate_term(sort)),
                ));
            }
        });

        EunoiaTerm::List(ret)
    }

    fn translate_operator(operator: Operator) -> Symbol {
        match operator {
            // TODO: put this into theory.rs
            // Boolean operators.
            Operator::Xor => String::from("xor"),

            Operator::Not => String::from("not"),

            // Order / Comparison.
            Operator::Equals => String::from("="),

            Operator::GreaterThan => String::from(">"),

            Operator::GreaterEq => String::from(">="),

            Operator::LessThan => String::from("<"),

            Operator::LessEq => String::from("<="),

            _ => String::from("not"),
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

    fn translate_proof_arg(&self, proof_arg: &ProofArg) -> EunoiaTerm {
        match proof_arg {
            // An argument that is just a term.
            ProofArg::Term(term) => self.translate_term(term),

            ProofArg::Assign(.., term) => {
                // TODO: how should we translate (:= <symbol> <term>)?
                self.translate_term(term)
            }
        }
    }

    /// Implements the translation of an Alethe `ProofStep`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed within Eunoia.
    fn translate_step(
        &mut self,
        id: &str,
        clause: &[Rc<Term>],
        rule: &str,
        premises: &[(usize, usize)],
        args: &[ProofArg],
        proof_iter: &ProofIter<'_>,
    ) {
        let mut alethe_premises: Vec<EunoiaTerm> = Vec::new();
        // Add contextual premises.
        alethe_premises.extend_from_slice(&self.contextual_premises);
        // Add remaining premises, actually present in the original step command.
        alethe_premises.extend(
            premises
                .iter()
                .map(|pair| EunoiaTerm::Id(String::from(proof_iter.get_premise(*pair).id())))
                .collect::<Vec<EunoiaTerm>>(),
        );

        // NOTE: in ProofStep, clause has type
        // Vec<Rc<Term>>, though it represents an
        // invocation of Alethe's cl operator
        // TODO: we are always adding the conclusion clause
        let conclusion: EunoiaTerm = EunoiaTerm::App(
            self.alethe_signature.cl.clone(),
            clause
                .iter()
                .map(|term| self.translate_term(term))
                .collect(),
        );

        // NOTE: not adding conclusion clause to this list
        let mut eunoia_arguments: Vec<EunoiaTerm> = Vec::new();

        args.iter().for_each(|arg| {
            eunoia_arguments.push(self.translate_proof_arg(arg));
        });

        match rule {
            "let" => {
                self.eunoia_proof.push(EunoiaCommand::StepPop {
                    name: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: self.alethe_signature.let_rule.clone(),
                    premises: EunoiaList { list: alethe_premises },
                    arguments: EunoiaList { list: eunoia_arguments },
                });
            }

            _ => {
                self.eunoia_proof.push(EunoiaCommand::Step {
                    name: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: rule.to_owned(),
                    premises: EunoiaList { list: alethe_premises },
                    arguments: EunoiaList { list: eunoia_arguments },
                });
            }
        }
    }

    // TODO: make eunoia_prelude an attribute of EunoiaTranslator
    /// Translates only an SMT-lib problem prelude.
    pub fn translate_problem_prelude(&self, prelude: &ProblemPrelude) -> EunoiaProof {
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
            eunoia_prelude.push(EunoiaCommand::DeclareType {
                name: pair.0.clone(),
                kind: EunoiaList { list: vec![] },
            });
        });

        function_declarations.iter().for_each(|pair| {
            eunoia_prelude.push(EunoiaCommand::DeclareConst {
                name: pair.0.clone(),
                eunoia_type: self.translate_term(&pair.1),
                attrs: Vec::new(),
            });
        });

        eunoia_prelude
    }
}

impl Default for EunoiaTranslator {
    fn default() -> Self {
        Self::new()
    }
}

impl Translator for EunoiaTranslator {
    type Output = EunoiaProof;

    fn translate<'a>(&'a mut self, _proof: &Rc<ProofNode>) -> &'a Self::Output {
        self.translate(_proof)
    }
}
