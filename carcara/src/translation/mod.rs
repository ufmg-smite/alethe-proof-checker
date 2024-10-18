pub mod alethe_signature;
pub mod eunoia;
pub mod eunoia_ast;
pub mod printer;
pub mod tests;

use crate::ast::*;

pub trait Translator {
    type Output;

    fn translate<'a>(&'a mut self, proof: &Rc<ProofNode>) -> &'a Self::Output;
}
