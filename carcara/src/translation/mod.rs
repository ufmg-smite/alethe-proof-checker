pub mod alethe_signature;
pub mod eunoia;
pub mod eunoia_ast;
#[cfg(test)]
mod tests;

use crate::ast::*;

// TODO: why do we need to define/implement this trait?
pub trait Translator {
    // NOTE: needed to lifetime param. to deal with my EunoiaProof struct
    type Output;

    fn translate(&mut self, proof: &Rc<ProofNode>) -> Self::Output;
}
