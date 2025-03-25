//! Common imports for `motsu` tests.
pub use crate::{
    context::{
        Account, Balance, Contract, ContractCall, FromTag, Funding, VMContext,
    },
    precompiles::deploy_precompiles,
    revert::ResultExt,
};
