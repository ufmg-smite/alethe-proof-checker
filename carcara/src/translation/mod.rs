pub mod eunoia;

use crate::ast::*;

pub trait Translator {
    type Output;

    fn translate(&mut self, proof: &Rc<ProofNode>) -> Self::Output;
}
