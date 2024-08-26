pub mod eunoia;

use crate::ast::*;

trait Translator {
    type Output;

    fn translate(&mut self, proof: &Rc<ProofNode>) -> Self::Output;
}
