/// Definition of Alethe in Eunoia, following [AletheInAlf](https://github.com/cvc5/aletheinalf/).
use std::string::String;
// TODO: import everything once
use crate::translation::eunoia_ast::*;

// TODO: THIS IS ONLY DONE TO AVOID THE COMPLEXITIES OF DECLARING
// AND DEALING WITH GLOBALS IN RUST.
pub struct AletheTheory {
    // Built-in operators.
    pub cl: Symbol,
    pub ite: Symbol,

    // Logical operators.
    pub and: Symbol,

    // Comparison.
    pub eq: Symbol,
    pub lt: Symbol,
    pub le: Symbol,
    pub gt: Symbol,
    pub ge: Symbol,

    // Rules' names.
    pub let_rule: Symbol,

    // Context representation and manipulation.
    // To bind variables in a context.
    pub var: Symbol,

    // Binders.
    pub let_binder: Symbol,
}

impl AletheTheory {
    pub fn new() -> Self {
        AletheTheory {
            cl: String::from("@cl"),
            ite: String::from("ite"),

            // Logical operators.
            and: String::from("and"),

            // Comparison.
            eq: String::from("="),
            lt: String::from("<"),
            le: String::from("<="),
            gt: String::from(">"),
            ge: String::from(">="),

            // Rules' names.
            let_rule: String::from("let_elim"),

            // Context representation and manipulation.
            var: String::from("@var"),

            // Binders.
            let_binder: String::from("@let"),
        }
    }
}

impl Default for AletheTheory {
    fn default() -> Self {
        AletheTheory::new()
    }
}
