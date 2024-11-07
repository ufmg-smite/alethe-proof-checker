//! Translator for `EunoiaProof`.
use super::Translator;
use crate::ast::*;
use crate::translation::alethe_signature::theory::*;
use crate::translation::eunoia_ast::*;

use std::collections::HashMap;
// Deref for ast::rc::Rc<Term>
use std::ops::Deref;

pub struct EunoiaTranslator {
    /// Actual `EunoiaProof` object containing the translation.
    eunoia_proof: EunoiaProof,

    // TODO: declared as attributes to avoid
    // "cannot move out... a captured variable in an `FnMut` closure" errors
    // TODO: declared as Vec<ProofNode> (not using borrows) to avoid
    // error "borrowed data escapes outside of closure"
    /// Auxiliary attributes useful to maintain a pre-ordered version
    /// of the `ProofNode` graph.
    pre_ord_proof_node: Vec<ProofNode>,
    aux_pre_ord_proof_node: Vec<ProofNode>,

    // TODO: see for a better way of including Alethe's signature
    // We are not including it into the Pool of terms
    /// "Alethe in Eunoia" signature considered during translation.
    alethe_signature: AletheTheory,

    /// Mapping variable -> sort for variables in scope, as introduced by
    /// Alethe's 'anchor' command.
    // TODO: would it be useful to use borrows?
    // TODO: not taking into account fixed variables in context
    variables_in_scope: HashMap<String, EunoiaTerm>,

    /// Counter for contexts opened: useful for naming context and reasoning
    /// about context opening.
    contexts_opened: usize,

    /// Maintains references to previous steps from the actual sub-proof.
    local_steps: Vec<Vec<usize>>,
}

impl EunoiaTranslator {
    pub fn new() -> Self {
        Self {
            eunoia_proof: Vec::new(),
            pre_ord_proof_node: Vec::new(),
            aux_pre_ord_proof_node: Vec::new(),
            alethe_signature: AletheTheory::new(),
            variables_in_scope: HashMap::new(),
            contexts_opened: 0,
            local_steps: Vec::new(),
        }
    }

    pub fn translate<'a>(&'a mut self, proof: &Rc<ProofNode>) -> &'a EunoiaProof {
        // Clean previously created data.
        if self.contexts_opened > 0 {
            self.eunoia_proof = Vec::new();
            self.pre_ord_proof_node = Vec::new();
            self.aux_pre_ord_proof_node = Vec::new();
            self.variables_in_scope = HashMap::new();
            self.contexts_opened = 0;
            self.local_steps = Vec::new();
        }

        // TODO: Subproof has a context_id that could be used instead of contexts_opened
        // TODO: is it possible to define a private name-space prefixing some
        // symbol?
        // Counter for contexts opened
        // { self.contexts_opened == 0 }
        let context_name = String::from("ctx") + &self.contexts_opened.to_string();

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

        self.contexts_opened += 1;

        self.local_steps.push(Vec::new());

        // NOTE: need to clone ProofNodes to avoid
        // "borrowed data escapes outside of closure" error here.
        proof.traverse(|node: &Rc<ProofNode>| {
            self.post_order_to_list(node);
        });

        self.translate_pre_ord_proof_node();

        &self.eunoia_proof
    }

    // TODO: aux method that shouldn't be here
    // TODO: is there some practical way of doing partial application of
    // procedures? Quick fix: transferring ownership of vectors
    fn post_order_to_list(&mut self, node: &Rc<ProofNode>) {
        match (*node).deref() {
            ProofNode::Assume { .. } => {
                self.pre_ord_proof_node.push((*node).deref().clone());
            }

            ProofNode::Step(StepNode { id: _, depth, .. }) => {
                if *depth > 0 {
                    // This is a node from a subproof.
                    self.aux_pre_ord_proof_node.push((*node).deref().clone());
                } else {
                    // { depth == 0}
                    // This is not a node from a subproof, we can safely push it
                    // into pre_ord_proof_node.
                    self.pre_ord_proof_node.push((*node).deref().clone());
                }
            }

            // A subproof introduced by the 'anchor' command.
            ProofNode::Subproof(..) => {
                self.pre_ord_proof_node.push((*node).deref().clone());
                self.pre_ord_proof_node
                    .append(&mut self.aux_pre_ord_proof_node);
            }
        }
    }

    fn translate_pre_ord_proof_node(&mut self) {
        // NOTE: cloning to avoid error
        // "closure requires unique access to `*self` but it is already borrowed//
        self.pre_ord_proof_node.clone().iter().for_each(|node| {
            match node {
                ProofNode::Assume { id, depth: _, term } => {
                    self.eunoia_proof.push(
                        // TODO: what about :named?
                        EunoiaCommand::Assume {
                            name: id.clone(),
                            term: self.translate_term(term),
                        },
                    );
                }

                ProofNode::Step(StepNode {
                    id,
                    depth: _,
                    clause,
                    rule,
                    premises,
                    args,
                    ..
                }) => {
                    self.eunoia_proof
                        .push(self.translate_step(id, clause, rule, premises, args));
                    // Keep a reference to the
                    self.local_steps[self.contexts_opened - 1].push(self.eunoia_proof.len() - 1);
                }

                // A subproof introduced by the 'anchor' command.
                ProofNode::Subproof(SubproofNode { last_step: _, args, .. }) => {
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
                                vec![EunoiaTerm::Id(name.clone()), self.translate_term(term)],
                            ));

                            ctx_typed_params.push(EunoiaTerm::List(vec![
                                EunoiaTerm::Id(name.clone()),
                                self.translate_term(sort),
                            ]));
                        }
                    });
                    // TODO: do not hard-code this string
                    // TODO: ugly!
                    and_params.push(EunoiaTerm::Id(
                        String::from("ctx") + &(self.contexts_opened - 1).to_string(),
                    ));

                    // Add typed params.
                    ctx_params.push(EunoiaTerm::List(ctx_typed_params));

                    // Concat (and...)
                    ctx_params.push(EunoiaTerm::App(
                        self.alethe_signature.and.clone(),
                        and_params,
                    ));

                    // Define and open a new context
                    // (define ctxn () (@ctx ...))
                    // TODO: do not hard-code this string
                    let context_name = String::from("ctx") + &self.contexts_opened.to_string();

                    // Close the opened sub-proof
                    self.eunoia_proof.push(EunoiaCommand::Define {
                        name: context_name.clone(),
                        typed_params: EunoiaList { list: Vec::new() },
                        // TODO: define @ctx in theory.rs
                        term: EunoiaTerm::App(String::from("@ctx"), ctx_params),
                        attrs: Vec::new(),
                    });

                    // (assume-push context ctxn)
                    self.eunoia_proof.push(EunoiaCommand::AssumePush {
                        name: String::from("context"),
                        term: EunoiaTerm::Id(context_name.clone()),
                    });

                    // New context opened...
                    self.contexts_opened += 1;
                    self.local_steps.push(Vec::new());

                    // TODO: clean contextual assumptions and var. defs.
                }
            }
        });
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
            // Logic
            Operator::And => String::from("and"),

            Operator::Or => String::from("or"),

            Operator::Xor => String::from("xor"),

            Operator::Not => String::from("not"),

            Operator::Implies => String::from("=>"),

            Operator::Ite => String::from("ite"),

            // Order / Comparison.
            Operator::Equals => String::from("="),

            Operator::GreaterThan => String::from(">"),

            Operator::GreaterEq => String::from(">="),

            Operator::LessThan => String::from("<"),

            Operator::LessEq => String::from("<="),

            Operator::Distinct => String::from("distinct"),

            // Arithmetic
            Operator::Add => String::from("+"),

            Operator::Sub => String::from("-"),

            Operator::Mult => String::from("*"),

            Operator::IntDiv => String::from("div"),

            Operator::RealDiv => String::from("/"),

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

            Sort::Function(sorts) => {
                // TODO: is this correct?
                assert!(sorts.len() >= 2,);

                let return_sort;

                match sorts.last() {
                    Some(term) => {
                        match (*term).deref() {
                            Term::Sort(sort) => {
                                return_sort = EunoiaTranslator::translate_sort(sort);
                            }

                            _ => {
                                // TODO: is this correct?
                                panic!();
                            }
                        }
                    }

                    None => {
                        // TODO: is this correct?
                        panic!();
                    }
                };

                let mut sorts_params = Vec::new();

                for (pos, rc_sort) in sorts.iter().enumerate() {
                    if pos < sorts.len() - 1 {
                        match rc_sort.deref() {
                            Term::Sort(sort) => {
                                sorts_params.push(EunoiaTranslator::translate_sort(sort));
                            }

                            _ => {
                                // TODO: is this correct?
                                panic!();
                            }
                        }
                    }
                }

                // TODO: no attrs?
                EunoiaType::Fun(vec![], sorts_params, Box::new(return_sort))
            }

            Sort::Bool => EunoiaType::Bool,

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
        &self,
        id: &str,
        clause: &[Rc<Term>],
        rule: &str,
        premises: &[Rc<ProofNode>],
        args: &[ProofArg],
    ) -> EunoiaCommand {
        let command: EunoiaCommand;
        let mut alethe_premises: Vec<EunoiaTerm> = Vec::new();

        // Add remaining premises, actually present in the original step command.
        alethe_premises.extend(
            premises
                .iter()
                .map(|node| EunoiaTerm::Id(String::from(node.deref().id())))
                .collect::<Vec<EunoiaTerm>>(),
        );

        // NOTE: in ProofStep, clause has type
        // Vec<Rc<Term>>, though it represents an
        // invocation of Alethe's cl operator
        // TODO: we are always adding the conclusion clause
        let conclusion: EunoiaTerm = if clause.is_empty() {
            EunoiaTerm::Id(self.alethe_signature.empty_cl.clone())
        } else {
            // {!clause.is_empty()}
            EunoiaTerm::App(
                self.alethe_signature.cl.clone(),
                clause
                    .iter()
                    .map(|term| self.translate_term(term))
                    .collect(),
            )
        };

        // NOTE: not adding conclusion clause to this list
        let mut eunoia_arguments: Vec<EunoiaTerm> = Vec::new();

        args.iter().for_each(|arg| {
            eunoia_arguments.push(self.translate_proof_arg(arg));
        });

        // TODO: develop some generic programmatic way to deal with each rule's
        // semantics (as explained in theory.rs) instead of this
        match rule {
            "let" => {
                // TODO: do not hard-code this string
                eunoia_arguments.push(EunoiaTerm::Id("context".to_owned()));

                // Extract lhs and rhs
                let (lhs, rhs) = AletheTheory::extract_eq_lhs_rhs(&conclusion);
                eunoia_arguments.push(lhs);
                eunoia_arguments.push(rhs);

                // Include, as premises, previous steps from the actual sub-proof.
                self.local_steps[self.contexts_opened - 1]
                    .iter()
                    .for_each(|index| {
                        match &self.eunoia_proof[*index] {
                            EunoiaCommand::Step { name, .. } => {
                                alethe_premises.push(EunoiaTerm::Id(name.clone()));
                            }

                            _ => {
                                // NOTE: it shouldn't an index to something different
                                // than a step.
                                panic!();
                            }
                        }
                    });

                command = EunoiaCommand::StepPop {
                    name: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: self.alethe_signature.let_rule.clone(),
                    premises: EunoiaList { list: alethe_premises },
                    arguments: EunoiaList { list: eunoia_arguments },
                };
            }

            "refl" => {
                // TODO: do not hard-code this string
                eunoia_arguments.push(EunoiaTerm::Id("context".to_owned()));

                // Extract lhs and rhs
                let (lhs, rhs) = AletheTheory::extract_eq_lhs_rhs(&conclusion);

                eunoia_arguments.push(lhs);

                eunoia_arguments.push(rhs);

                command = EunoiaCommand::Step {
                    name: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: self.alethe_signature.refl.clone(),
                    premises: EunoiaList { list: alethe_premises },
                    arguments: EunoiaList { list: eunoia_arguments },
                };
            }

            "equiv_pos2" => {
                command = EunoiaCommand::Step {
                    name: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: self.alethe_signature.equiv_pos2.clone(),
                    premises: EunoiaList { list: alethe_premises },
                    arguments: EunoiaList { list: eunoia_arguments },
                };
            }

            _ => {
                command = EunoiaCommand::Step {
                    name: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: rule.to_owned(),
                    premises: EunoiaList { list: alethe_premises },
                    arguments: EunoiaList { list: eunoia_arguments },
                };
            }
        }

        command
    }

    // TODO: make eunoia_prelude an attribute of EunoiaTranslator
    /// Translates only an SMT-lib problem prelude.
    pub fn translate_problem_prelude(&self, prelude: &ProblemPrelude) -> EunoiaProof {
        let ProblemPrelude {
            sort_declarations,
            function_declarations,
            ..
        } = prelude;

        let mut eunoia_prelude = Vec::new();

        // TODO: ethos does not accept set-logics
        // match logic {
        //     Some(logic_name) => {
        //         eunoia_prelude.push(EunoiaCommand::SetLogic { name: logic_name.clone() });
        //     }

        //     None => {}
        // }

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
