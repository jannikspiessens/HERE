use proofs::{commit::DPCS, codes::DFC};

pub mod basefold;


// Default
pub type DBPCS<'a, F, const LOG: bool> = crate::commit::basefold::BlindFoldPCS<'a,
    DFC<'a, F>,
    proofs::commit::basefold::BaseFoldSumcheckDoubleEfficient<'a, F>,
LOG>;

