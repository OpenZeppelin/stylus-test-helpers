//! Ethereum Precompiles
use stylus_sdk::storage::StorageType;

use crate::context::Contract;

pub(crate) mod ecrecover;

mod errors;

/// Deploy precompiled contracts.
///
/// Returns a vector of the contracts to ensure the compiler doesn't drop the
/// contracts.
///
/// See: <https://ethereum.github.io/yellowpaper/paper.pdf>
#[must_use]
pub fn deploy_precompiles() -> Vec<Contract<impl StorageType>> {
    vec![Contract::<ecrecover::EcRecover>::new_at(ecrecover::ADDRESS)]
}
