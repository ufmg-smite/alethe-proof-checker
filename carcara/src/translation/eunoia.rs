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
    /// Auxiliary attribute useful to maintain a pre-ordered version
    /// of the `ProofNode` graph.
    pre_ord_proof: Vec<ProofNode>,

    // TODO: this should be a variable local to post_order_to_list
    /// Depth of the previous node visited.
    previous_depth: usize,

    /// Auxiliary attribute useful to maintain a pre-ordered version
    /// of every node from a subproof with depth bigger than 1.
    pre_ord_subproofs: Vec<Vec<ProofNode>>,

    // TODO: see for a better way of including Alethe's signature
    // We are not including it into the Pool of terms
    /// "Alethe in Eunoia" signature considered during translation.
    alethe_signature: AletheTheory,

    /// Mapping variable -> sort for variables in scope, as introduced by
    /// Alethe's 'anchor' command.
    // TODO: would it be useful to use borrows?
    // TODO: not taking into account fixed variables in context
    variables_in_scope: Vec<HashMap<String, EunoiaTerm>>,

    /// Flags that indicate if the context of a given index has been
    /// actually introduced in the certificate through an Eunoia definition.
    context_introduced: Vec<bool>,

    /// Counter for contexts opened: useful for naming context and reasoning
    /// about context opening.
    contexts_opened: usize,

    /// Maintains references to previous steps from the actual subproof.
    local_steps: Vec<Vec<usize>>,

    /// Rule and id of the last step from the actual subproof, if any.
    last_step_rule: Vec<String>,

    last_step_id: Vec<String>,
}

impl EunoiaTranslator {
    pub fn new() -> Self {
        Self {
            eunoia_proof: Vec::new(),
            pre_ord_proof: Vec::new(),
            previous_depth: 0,
            pre_ord_subproofs: Vec::new(),
            alethe_signature: AletheTheory::new(),
            variables_in_scope: Vec::new(),
            context_introduced: Vec::new(),
            contexts_opened: 0,
            local_steps: Vec::new(),
            last_step_rule: Vec::new(),
            last_step_id: Vec::new(),
        }
    }

    pub fn translate<'a>(&'a mut self, proof: &Rc<ProofNode>) -> &'a EunoiaProof {
        // Clean previously created data.
        if self.contexts_opened > 0 {
            self.eunoia_proof = Vec::new();
            self.pre_ord_proof = Vec::new();
            self.previous_depth = 0;
            self.pre_ord_subproofs = Vec::new();
            self.variables_in_scope = Vec::new();
            self.context_introduced = Vec::new();
            self.contexts_opened = 0;
            self.local_steps = Vec::new();
            self.last_step_rule = Vec::new();
            self.last_step_id = Vec::new();
        }

        // TODO: Subproof has a context_id that could be used instead of contexts_opened
        // TODO: is it possible to define a private name-space prefixing some
        // symbol?
        // Some rules query the context (e.g., refl). We need to always have
        // opened at least one context
        // Counter for contexts opened
        // { self.contexts_opened == 0 }
        self.contexts_opened += 1;
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

        self.variables_in_scope.push(HashMap::new());

        // No new variables introduced in this first "global" context.
        self.context_introduced.push(true);

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
    // procedures? Quick fix: using attributes (aux_pre_ord_proof_node, etc)
    fn post_order_to_list(&mut self, node: &Rc<ProofNode>) {
        match (*node).deref() {
            ProofNode::Assume { id: _, depth, .. } => {
                if *depth > self.previous_depth {
                    // A new subproof
                    // TODO: ugly
                    while self.pre_ord_subproofs.len() < *depth {
                        self.pre_ord_subproofs.push(Vec::new());
                    }

                    // { self.pre_ord_subproofs.len() >= *depth }

                    self.pre_ord_subproofs[*depth - 1].push((*node).deref().clone());
                } else {
                    // { *depth <= self.previous_depth }
                    if *depth == 0 {
                        // This is not a node from a subproof, we can safely push it
                        // into pre_ord_proof_node.
                        self.pre_ord_proof.push((*node).deref().clone());
                    } else {
                        // { *depth > 0 }
                        // We are still within a subproof
                        assert!(self.pre_ord_subproofs.len() >= *depth - 1);
                        self.pre_ord_subproofs[*depth - 1].push((*node).deref().clone());
                    }
                }

                self.previous_depth = *depth;
            }

            ProofNode::Step(StepNode { id: _, depth, .. }) => {
                if *depth > self.previous_depth {
                    // A new subproof
                    // TODO: ugly
                    while self.pre_ord_subproofs.len() < *depth {
                        self.pre_ord_subproofs.push(Vec::new());
                    }

                    // { self.pre_ord_subproofs.len() >= *depth }
                    self.pre_ord_subproofs[*depth - 1].push((*node).deref().clone());
                } else {
                    // { *depth <= self.previous_depth }
                    if *depth == 0 {
                        // This is not a node from a subproof, we can safely push it
                        // into pre_ord_proof_node.
                        self.pre_ord_proof.push((*node).deref().clone());
                    } else {
                        // { *depth > 0 }
                        // We are still within a subproof
                        assert!(self.pre_ord_subproofs.len() >= *depth);
                        self.pre_ord_subproofs[*depth - 1].push((*node).deref().clone());
                    }
                }

                self.previous_depth = *depth;
            }

            // A subproof introduced by the 'anchor' command.
            ProofNode::Subproof(SubproofNode { last_step, .. }) => {
                match (*last_step).deref() {
                    ProofNode::Step(StepNode { id: _, depth, .. }) => {
                        assert!(1 <= *depth && *depth == self.previous_depth);

                        if *depth == 1 {
                            // Outermost subproof: we return to self.pre_ord_proof
                            self.pre_ord_proof.push((*node).deref().clone());
                            self.pre_ord_proof
                                .append(&mut self.pre_ord_subproofs[*depth - 1]);
                        } else {
                            // { depth > 1 }
                            // UNSAFE
                            let (left_slice, right_slice) =
                                self.pre_ord_subproofs.split_at_mut(*depth - 1);
                            left_slice[*depth - 2].push((*node).deref().clone());
                            left_slice[*depth - 2].append(&mut right_slice[0]);
                        }

                        // Pop the subproof being closed
                        self.pre_ord_subproofs.pop();

                        self.previous_depth = *depth;
                    }

                    _ => {
                        // It shouldn't be a ProofNode different than a Step
                        panic!();
                    }
                }
            }
        }
    }

    /// For a given "nesting" level (some number <= `self.contexts_opened`),
    /// returns the index of the last surrounding context actually introduced
    /// within the proof certificate, with an Eunoia definition.
    /// PRE: { 0 < `nesting_level` < `self.contexts_opened`}
    fn get_last_introduced_context(&self, nesting_level: usize) -> usize {
        let mut last_scope: usize = 0;

        for i in 0..nesting_level {
            if self.context_introduced[nesting_level - 1 - i] {
                last_scope = nesting_level - 1 - i;
                break;
            }
        }

        last_scope
    }

    /// Implements the actual translation logic, after the original `ProofNode` graph
    /// has been translated into a list of `ProofNodes`.
    /// PRE : {!`self.local_steps.is_empty()`}
    fn translate_pre_ord_proof_node(&mut self) {
        // NOTE: cloning to avoid error
        // "closure requires unique access to `*self` but it is already borrowed//
        self.pre_ord_proof.clone().iter().for_each(|node| {
            match node {
                ProofNode::Assume { id, depth, term } => {
                    self.eunoia_proof.push(
                        // TODO: what about :named?
                        self.translate_assume(id, *depth, term),
                    );
                }

                ProofNode::Step(StepNode {
                    id,
                    depth: _,
                    clause,
                    rule,
                    premises,
                    args,
                    discharge,
                    ..
                }) => {
                    self.translate_step(id, clause, rule, premises, args, discharge);

                    // If within a subproof: save the index for future reference
                    self.local_steps[self.contexts_opened - 1].push(self.eunoia_proof.len() - 1);

                    // Is this the closing step of the actual subproof?
                    if !self.last_step_id.is_empty() {
                        let last_step_id = &self.last_step_id.last();
                        if *last_step_id == Some(id) {
                            // TODO: ugly, hacky way of dealing with
                            // "bind" rule already doing a step-pop of the pushed
                            // context
                            assert!(self.last_step_rule.len() == self.last_step_id.len());

                            if self.context_introduced[self.contexts_opened - 1]
                                && self.last_step_rule.last()
                                    != Some(&self.alethe_signature.bind.clone())
                            {
                                self.eunoia_proof.push(EunoiaCommand::StepPop {
                                    // TODO: change id
                                    id: id.to_owned(),
                                    conclusion_clause: Some(EunoiaTerm::Id(
                                        self.alethe_signature.empty_cl.clone(),
                                    )),
                                    rule: self.alethe_signature.discard_context.clone(),
                                    premises: EunoiaList { list: vec![] },
                                    arguments: EunoiaList { list: vec![] },
                                });
                            }

                            self.last_step_rule.pop();
                            self.last_step_id.pop();

                            // Closing the context...
                            self.contexts_opened -= 1;
                            self.local_steps.pop();
                            self.variables_in_scope.pop();
                            self.context_introduced.pop();
                        }
                    }
                }

                // A subproof introduced by the 'anchor' command.
                ProofNode::Subproof(SubproofNode { last_step, args, .. }) => {
                    // To store @VarList parameters to @ctx
                    let mut ctx_params = Vec::new();
                    let mut ctx_typed_params = Vec::new();
                    // To store actual parameters of 'and'
                    let mut and_params: Vec<EunoiaTerm> = Vec::new();
                    // Dummy initial value
                    let mut eunoia_sort: EunoiaTerm = EunoiaTerm::True;

                    // New context opened. For scope reasoning purpose, we do this even
                    // if the anchor command does not introduce new variables (
                    // TODO: poor performance
                    // Maintain variables from previous scope...
                    self.variables_in_scope
                        .push(self.variables_in_scope[self.contexts_opened - 1].clone());
                    self.contexts_opened += 1;
                    self.local_steps.push(Vec::new());

                    if args.is_empty() {
                        self.context_introduced.push(false);
                    } else {
                        // { !args.is_empty() }
                        // We actually have an anchor introducing new variables

                        self.context_introduced.push(true);
                        args.iter().for_each(|arg| match arg {
                            AnchorArg::Variable((name, sort)) => {
                                // TODO: either use borrows or implement
                                // Copy trait for EunoiaTerms
                                if !self.variables_in_scope[self.contexts_opened - 1]
                                    .contains_key(name)
                                {
                                    eunoia_sort = self.translate_term(sort);
                                    // Add variables to the current scope.
                                    self.variables_in_scope[self.contexts_opened - 1]
                                        .insert(name.clone(), eunoia_sort.clone());
                                }

                                ctx_typed_params.push(EunoiaTerm::List(vec![
                                    EunoiaTerm::Id(name.clone()),
                                    self.translate_term(sort),
                                ]));
                            }
                            AnchorArg::Assign((name, sort), term) => {
                                // TODO: either use borrows or implement
                                // Copy trait for EunoiaTerms
                                // Add variables to the current scope.
                                if !self.variables_in_scope[self.contexts_opened - 1]
                                    .contains_key(name)
                                {
                                    eunoia_sort = self.translate_term(sort);
                                    self.variables_in_scope[self.contexts_opened - 1]
                                        .insert(name.clone(), eunoia_sort.clone());

                                    ctx_typed_params.push(EunoiaTerm::List(vec![
                                        EunoiaTerm::Id(name.clone()),
                                        self.translate_term(sort),
                                    ]));
                                }

                                // TODO: ugly patch...
                                let rhs: EunoiaTerm = match term.deref() {
                                    Term::Var(string, _) => EunoiaTerm::Id(string.clone()),

                                    _ => self.translate_term(term),
                                };

                                and_params.push(EunoiaTerm::App(
                                    self.alethe_signature.eq.clone(),
                                    vec![EunoiaTerm::Id(name.clone()), rhs],
                                ));
                            }
                        });
                        // TODO: do not hard-code this string
                        // TODO: ugly!
                        and_params.push(EunoiaTerm::Id(
                            String::from("ctx")
                                + &(self.get_last_introduced_context(self.contexts_opened - 1) + 1)
                                    .to_string(),
                        ));

                        // Add typed params.
                        if ctx_typed_params.is_empty() {
                            // Empty VarList
                            ctx_params
                                .push(EunoiaTerm::Id(self.alethe_signature.varlist_nil.clone()));
                        } else {
                            // TODO: shouldn' we build it with @varlist?
                            ctx_params.push(EunoiaTerm::List(ctx_typed_params));
                        }

                        // Concat (and...)
                        ctx_params.push(EunoiaTerm::App(
                            self.alethe_signature.and.clone(),
                            and_params,
                        ));

                        // Define and open a new context
                        // (define ctxn () (@ctx ...))
                        // TODO: do not hard-code this string
                        let context_name = String::from("ctx") + &self.contexts_opened.to_string();

                        // Close the opened subproof
                        self.eunoia_proof.push(EunoiaCommand::Define {
                            name: context_name.clone(),
                            typed_params: EunoiaList { list: Vec::new() },
                            // TODO: define @ctx in theory.rs
                            term: EunoiaTerm::App(String::from("@ctx"), ctx_params),
                            attrs: Vec::new(),
                        });

                        // TODO: should we step-pop this context, when closing the
                        // scope?
                        // (assume-push context ctxn)
                        self.eunoia_proof.push(EunoiaCommand::AssumePush {
                            name: String::from("context"),
                            term: EunoiaTerm::Id(context_name.clone()),
                        });
                    }

                    // Save information about the last step of the subproof
                    match (*last_step).deref() {
                        ProofNode::Step(StepNode {
                            id: last_step_id,
                            depth: _,
                            clause: _,
                            rule: last_step_rule,
                            ..
                        }) => {
                            self.last_step_rule.push(last_step_rule.clone());
                            self.last_step_id.push(last_step_id.clone());
                        }

                        _ => {
                            // It shouldn't be something different then a step
                            panic!();
                        }
                    }

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

                    _ => EunoiaTerm::App(self.translate_operator(*operator), operands_eunoia),
                }
            }

            // TODO: not considering the sort of the variable.
            Term::Var(string, _) => {
                // Check if it is a context variable.
                if !self.variables_in_scope.is_empty()
                    && self.variables_in_scope[self.contexts_opened - 1].contains_key(string)
                {
                    // TODO: abstract this into a procedure
                    EunoiaTerm::App(
                        self.alethe_signature.var.clone(),
                        vec![
                            EunoiaTerm::List(vec![EunoiaTerm::List(vec![
                                EunoiaTerm::Id(string.clone()),
                                // TODO: using clone, ugly...
                                self.variables_in_scope[self.contexts_opened - 1][string].clone(),
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

            Term::Binder(binder, binding_list, scope) => {
                match binder {
                    Binder::Forall => EunoiaTerm::App(
                        self.alethe_signature.forall_binder.clone(),
                        vec![
                            self.translate_binding_list(binding_list),
                            self.translate_term(scope),
                        ],
                    ),

                    Binder::Exists => EunoiaTerm::App(
                        self.alethe_signature.exists_binder.clone(),
                        vec![
                            self.translate_binding_list(binding_list),
                            self.translate_term(scope),
                        ],
                    ),

                    // TODO: complete
                    _ => EunoiaTerm::App(
                        self.alethe_signature.exists_binder.clone(),
                        vec![
                            self.translate_binding_list(binding_list),
                            self.translate_term(scope),
                        ],
                    ),
                }
            }

            // TODO: complete
            Term::ParamOp { .. } => EunoiaTerm::True,
        }
    }

    fn translate_binding_list(&self, binding_list: &BindingList) -> EunoiaTerm {
        let mut ret = Vec::new();

        binding_list.iter().for_each(|sorted_var| {
            let (name, sort) = sorted_var;
            if !self.variables_in_scope.is_empty()
                && self.variables_in_scope[self.contexts_opened - 1].contains_key(name)
            {
                // TODO: abstract this into a procedure
                ret.push(EunoiaTerm::Var(
                    name.clone(),
                    Box::new(self.variables_in_scope[self.contexts_opened - 1][name].clone()),
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

    fn translate_operator(&self, operator: Operator) -> Symbol {
        match operator {
            // TODO: put this into theory.rs
            // Logic
            Operator::And => self.alethe_signature.and.clone(),

            Operator::Or => self.alethe_signature.or.clone(),

            Operator::Xor => String::from("xor"),

            Operator::Not => self.alethe_signature.not.clone(),

            Operator::Implies => String::from("=>"),

            Operator::Ite => String::from("ite"),

            // Order / Comparison.
            Operator::Equals => self.alethe_signature.eq.clone(),

            Operator::GreaterThan => self.alethe_signature.gt.clone(),

            Operator::GreaterEq => self.alethe_signature.ge.clone(),

            Operator::LessThan => self.alethe_signature.lt.clone(),

            Operator::LessEq => self.alethe_signature.le.clone(),

            Operator::Distinct => String::from("distinct"),

            // Arithmetic
            Operator::Add => self.alethe_signature.add.clone(),

            Operator::Sub => self.alethe_signature.sub.clone(),

            Operator::Mult => self.alethe_signature.mult.clone(),

            Operator::IntDiv => self.alethe_signature.int_div.clone(),

            Operator::RealDiv => self.alethe_signature.real_div.clone(),

            _ => {
                println!("No defined translation for operator {:?}", operator);
                panic!()
            }
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

    /// Implements the translation of an Alethe `Assume`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed within Eunoia.
    fn translate_assume(&self, id: &str, _depth: usize, term: &Rc<Term>) -> EunoiaCommand {
        // Check last instruction in actual subproof
        let ret = if self.last_step_rule.is_empty() {
            // Regular introduction of assumptions
            EunoiaCommand::Assume {
                name: id.to_owned(),
                term: self.translate_term(term),
            }
        } else {
            match self.last_step_rule[self.last_step_rule.len() - 1].as_str() {
                // subproof receives every "assume" command as an actual
                // ethos assumption; we need to push every assumption
                "subproof" => EunoiaCommand::AssumePush {
                    name: id.to_owned(),
                    term: self.translate_term(term),
                },

                // Regular introduction of assumptions
                _ => EunoiaCommand::Assume {
                    name: id.to_owned(),
                    term: self.translate_term(term),
                },
            }
        };

        ret
    }

    /// Implements the translation of an Alethe `ProofStep`, taking into
    /// account technical differences in the way Alethe rules are
    /// expressed within Eunoia.
    /// Updates `self.eunoia_proof`.
    fn translate_step(
        &mut self,
        id: &str,
        clause: &[Rc<Term>],
        rule: &str,
        premises: &[Rc<ProofNode>],
        args: &[Rc<Term>],
        discharge: &[Rc<ProofNode>],
    ) {
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
            eunoia_arguments.push(self.translate_term(arg));
        });

        // TODO: develop some generic programmatic way to deal with each rule's
        // semantics (as explained in theory.rs) instead of this
        match rule {
            "la_generic" => {
                self.eunoia_proof.push(EunoiaCommand::Step {
                    id: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: self.alethe_signature.la_generic.clone(),
                    // TODO: should we check if alethe_premises == []?
                    premises: EunoiaList { list: vec![] },
                    // The coefficients are one single argument.  This means they
                    // must be be wrapped in a single function call using an n-ary
                    // function.
                    arguments: EunoiaList {
                        list: vec![EunoiaTerm::App(
                            self.alethe_signature.add.clone(),
                            eunoia_arguments,
                        )],
                    },
                });
            }

            "let" => {
                // TODO: do not hard-code this string
                eunoia_arguments.push(EunoiaTerm::Id("context".to_owned()));

                // Extract lhs and rhs
                let (lhs, rhs) = self.alethe_signature.extract_eq_lhs_rhs(&conclusion);
                eunoia_arguments.push(lhs);
                eunoia_arguments.push(rhs);

                // Include, as premises, previous steps from the actual subproof.
                self.local_steps[self.contexts_opened - 1]
                    .iter()
                    .for_each(|index| {
                        match &self.eunoia_proof[*index] {
                            EunoiaCommand::Step { id, .. } => {
                                alethe_premises.push(EunoiaTerm::Id(id.clone()));
                            }

                            _ => {
                                // NOTE: it shouldn't be an index to something different
                                // than a step.
                                panic!();
                            }
                        }
                    });

                self.eunoia_proof.push(EunoiaCommand::Step {
                    id: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: self.alethe_signature.let_rule.clone(),
                    premises: EunoiaList { list: alethe_premises },
                    arguments: EunoiaList { list: eunoia_arguments },
                });
            }

            "refl" => {
                // TODO: do not hard-code this string
                eunoia_arguments.push(EunoiaTerm::Id("context".to_owned()));

                // Extract lhs and rhs
                let (lhs, rhs) = self.alethe_signature.extract_eq_lhs_rhs(&conclusion);

                eunoia_arguments.push(lhs);

                eunoia_arguments.push(rhs);

                self.eunoia_proof.push(EunoiaCommand::Step {
                    id: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: self.alethe_signature.refl.clone(),
                    premises: EunoiaList { list: alethe_premises },
                    arguments: EunoiaList { list: eunoia_arguments },
                });
            }

            "bind" => {
                // :assumption: ctx
                self.eunoia_proof.push(EunoiaCommand::StepPop {
                    id: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: self.alethe_signature.bind.clone(),
                    premises: EunoiaList { list: alethe_premises },
                    arguments: EunoiaList { list: eunoia_arguments },
                });
            }

            "subproof" => {
                // TODO: check this
                // The command (as mechanized in Eunoia) gets the formula proven
                // through an "assumption", hence, we use StepPop.
                // The discharged assumptions (specified, in Alethe, through the
                // "discharge" formal parameter), will be pushed
                // NOTE: spurious value so the compiler won't comply
                let mut implied_conclusion: EunoiaTerm = EunoiaTerm::True;

                // Assuming that the conclusion is of the form
                // not φ1, ..., not φn, ψ
                // extract ψ
                let mut premise = EunoiaTerm::App(
                    self.alethe_signature.cl.clone(),
                    vec![self.alethe_signature.extract_consequent(&conclusion)],
                );

                let mut cl_disjuncts: Vec<EunoiaTerm> = vec![];

                // Id of the premise step
                let mut id_premise: Symbol = "".to_owned();

                discharge.iter().for_each(|assumption| {
                    // TODO: we are discarding vector premises
                    match assumption.deref() {
                        // TODO: ugly?
                        ProofNode::Assume { id: _, depth: _, term } => {
                            cl_disjuncts = vec![EunoiaTerm::App(
                                self.alethe_signature.not.clone(),
                                vec![self.translate_term(term)],
                            )];

                            cl_disjuncts
                                .append(&mut self.alethe_signature.extract_cl_disjuncts(&premise));

                            implied_conclusion = EunoiaTerm::App(
                                self.alethe_signature.cl.clone(),
                                // TODO: too much cloning...
                                cl_disjuncts.clone(),
                            );

                            // Get id of previous step
                            id_premise =
                                self.eunoia_proof[self.eunoia_proof.len() - 1].get_step_id();

                            self.eunoia_proof.push(EunoiaCommand::StepPop {
                                // TODO: change id!
                                // TODO: ethos does not complain about repeated ids
                                id: id.to_owned(),
                                conclusion_clause: Some(implied_conclusion.clone()),
                                rule: self.alethe_signature.subproof.clone(),
                                premises: EunoiaList {
                                    list: vec![EunoiaTerm::Id(id_premise.clone())],
                                },
                                arguments: EunoiaList { list: eunoia_arguments.clone() },
                            });

                            // TODO: too much cloning...
                            premise = implied_conclusion.clone();
                        }

                        _ => {
                            // TODO: it shouldn't be a ProofNode different than an Assume
                            panic!();
                        }
                    }
                });
            }

            "forall_inst" => {
                // TODO: we are discarding vector and premises arguments
                self.eunoia_proof.push(EunoiaCommand::Step {
                    id: id.to_owned(),
                    conclusion_clause: Some(conclusion),
                    rule: self.alethe_signature.forall_inst.clone(),
                    premises: EunoiaList { list: Vec::new() },
                    arguments: EunoiaList { list: Vec::new() },
                });
            }

            _ => {
                self.eunoia_proof.push(EunoiaCommand::Step {
                    id: id.to_owned(),
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
    pub fn translate_problem_prelude(&self, problem: &Problem) -> EunoiaProof {
        let Problem { prelude, .. } = problem;

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
