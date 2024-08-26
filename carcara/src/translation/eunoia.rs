use super::Translator;
use crate::ast::*;

// TODO
pub struct EunoiaProof;
pub struct EunoiaTranslator {}

impl Translator for EunoiaTranslator {
    type Output = EunoiaProof;

    fn translate(&mut self, _proof: &Rc<ProofNode>) -> Self::Output {
        todo!()
    }
}
