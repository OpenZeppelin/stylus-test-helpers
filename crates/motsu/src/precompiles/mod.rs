//! Ethereum Precompiles
use crate::context::Contract;

mod ecrecover;

/// Deploy precompiled contracts.
/// See: <https://ethereum.github.io/yellowpaper/paper.pdf>
pub fn deploy_precompiles() {
    _ = Contract::<ecrecover::EcRecover>::new_at(ecrecover::ADDRESS);
}
