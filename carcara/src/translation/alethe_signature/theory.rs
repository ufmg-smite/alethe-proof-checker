use crate::translation::eunoia_ast::*;

/// Definition of Alethe in Eunoia, following [AletheInAlf](https://github.com/cvc5/aletheinalf/).
use std::string::String;

// TODO: THIS IS ONLY DONE TO AVOID THE COMPLEXITIES OF DECLARING
// AND DEALING WITH GLOBALS IN RUST.
pub struct AletheTheory {
    // Built-in operators.
    pub cl: Symbol,
    // To represent the empty clause.
    pub empty_cl: Symbol,
    pub ite: Symbol,

    // Logical operators.
    pub and: Symbol,
    pub not: Symbol,
    pub or: Symbol,

    // Comparison.
    pub eq: Symbol,
    pub lt: Symbol,
    pub le: Symbol,
    pub gt: Symbol,
    pub ge: Symbol,

    // Rules' names.
    // TODO: order this
    pub let_rule: Symbol,
    pub equiv_pos2: Symbol,
    pub bind: Symbol,
    pub refl: Symbol,
    pub subproof: Symbol,
    pub forall_inst: Symbol,

    // Context representation and manipulation.
    // To bind variables in a context.
    pub var: Symbol,

    // Binders.
    pub let_binder: Symbol,
    pub forall_binder: Symbol,
    pub exists_binder: Symbol,

    // VarList constructors
    pub varlist_nil: Symbol,
}

impl AletheTheory {
    pub fn new() -> Self {
        AletheTheory {
            cl: String::from("@cl"),
            empty_cl: String::from("@empty_cl"),
            ite: String::from("ite"),

            // Logical operators.
            and: String::from("and"),
            or: String::from("or"),
            not: String::from("not"),

            // Comparison.
            eq: String::from("="),
            lt: String::from("<"),
            le: String::from("<="),
            gt: String::from(">"),
            ge: String::from(">="),

            // Rules' names.
            let_rule: String::from("let_elim"),
            refl: String::from("refl"),
            equiv_pos2: String::from("equiv_pos2"),
            subproof: String::from("subproof"),
            forall_inst: String::from("forall_inst"),
            bind: String::from("bind"),

            // Context representation and manipulation.
            var: String::from("@var"),

            // Binders.
            let_binder: String::from("@let"),
            forall_binder: String::from("forall"),
            exists_binder: String::from("exists"),

            // VarList constructors
            varlist_nil: String::from("@varlist.nil"),
        }
    }

    // Utilities to help in the translation of steps using specific rules.

    // Helps in extracting the lhs and rhs of a conclusion clause of
    // the form (@cl ("=", t1, t2)).
    // PRE: {conclusion is a EunoiaTerm of the form (@cl ("=", t1, t2)) }
    pub fn extract_eq_lhs_rhs(conclusion: &EunoiaTerm) -> (EunoiaTerm, EunoiaTerm) {
        match conclusion {
            // TODO: just assuming that cl and clause are correct
            EunoiaTerm::App(.., clause) => match clause.as_slice() {
                [EunoiaTerm::App(.., lhs_rhs)] => match lhs_rhs.as_slice() {
                    [lhs, rhs] => (lhs.clone(), rhs.clone()),
                    _ => panic!(),
                },

                _ => panic!(),
            },

            _ => {
                panic!();
            }
        }
    }
}

impl Default for AletheTheory {
    fn default() -> Self {
        AletheTheory::new()
    }
}
