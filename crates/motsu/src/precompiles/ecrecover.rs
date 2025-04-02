//! Contract simulating the precompiled `ecrecover` contract on-chain.
use alloy_primitives::Bytes;
use revm_precompile::secp256k1::{ec_recover_run, ECRECOVER};
use stylus_sdk::{alloy_primitives::Address, evm, prelude::*};

use super::errors::Error;

pub(crate) const ADDRESS: Address = ECRECOVER.0;

/// State of an [`EcRecover`] contract.
#[storage]
pub struct EcRecover;

/// NOTE: Implementation of [`TopLevelStorage`] to be able use `&mut self` when
/// calling other contracts and not `&mut (impl TopLevelStorage +
/// BorrowMut<Self>)`. Should be fixed in the future by the Stylus team.
unsafe impl TopLevelStorage for EcRecover {}

#[public]
impl EcRecover {
    /// Fallback function.
    #[allow(clippy::unused_self)]
    #[fallback]
    fn fallback(&self, calldata: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        ec_recover_run(&Bytes::copy_from_slice(calldata), evm::gas_left())
            .map(|out| output_to_left_padded_vec(&out.bytes))
            .map_err(Into::<Error>::into)
            .map_err(Into::into)
    }
}

/// Converts Bytes to a Vec<u8> with left-padding to ensure it's 32 bytes, as is
/// the behavior in Solidity.
///
/// Assumes the input Bytes will never be more than 32 bytes.
/// If the input Bytes is less than 32 bytes, the result will be left-padded
/// with zeroes.
///
/// See: <https://docs.soliditylang.org/en/v0.8.29/cheatsheet.html#mathematical-and-cryptographic-functions>
///
/// # Arguments
///
/// * `bytes` - The Bytes to convert (must be ≤ 32 bytes)
///
/// # Returns
///
/// A Vec<u8> containing exactly 32 bytes
fn output_to_left_padded_vec(bytes: &Bytes) -> Vec<u8> {
    let mut result = vec![0u8; 32];

    // Calculate the starting index in the result vector (for left padding)
    let start_index = 32 - bytes.len();

    result[start_index..].copy_from_slice(&bytes[..]);

    result
}

#[cfg(test)]
mod tests {
    use alloy_signer::SignerSync;
    use motsu::precompiles::ecrecover;
    use stylus_sdk::{
        alloy_primitives::{Address, B256},
        alloy_sol_types::{sol, SolValue},
        call::{self, Call},
        keccak_const::Keccak256,
        prelude::*,
    };

    use crate as motsu;
    use crate::prelude::*;

    sol! {
        /// Struct with callable data to the `ecrecover` precompile.
        #[allow(missing_docs)]
        struct EcRecoverData {
            /// EIP-191 Hash of the message.
            bytes32 hash;
            /// `v` value from the signature.
            uint8 v;
            /// `r` value from the signature.
            bytes32 r;
            /// `s` value from the signature.
            bytes32 s;
        }
    }

    fn encode_calldata(hash: B256, v: u8, r: B256, s: B256) -> Vec<u8> {
        let calldata = EcRecoverData { hash, v, r, s };
        EcRecoverData::abi_encode(&calldata)
    }

    #[storage]
    struct PrecompileAccessor;

    unsafe impl TopLevelStorage for PrecompileAccessor {}

    #[public]
    impl PrecompileAccessor {
        fn get_signer_address(
            &self,
            message: B256,
            v: u8,
            r: B256,
            s: B256,
        ) -> Result<Address, stylus_sdk::call::Error> {
            let calldata = encode_calldata(message, v, r, s);

            let recovered =
                call::static_call(Call::new(), ecrecover::ADDRESS, &calldata)?;

            Ok(Address::from_slice(&recovered[12..]))
        }
    }

    #[motsu::test]
    fn ecrecover(contract: Contract<PrecompileAccessor>, alice: Account) {
        let msg_hash = Keccak256::new()
            .update("Message to sign here.".as_bytes())
            .finalize()
            .into();

        // get v, r and s values
        let signature = alice.signer().sign_hash_sync(&msg_hash).unwrap();
        let recid: u8 = signature.recid().into();
        let (v, r, s) = (
            // ecrecover expects `v` to be in the range {27,28}
            recid + 27,
            signature.r().into(),
            signature.s().into(),
        );

        let address = contract
            .sender(alice)
            .get_signer_address(msg_hash, v, r, s)
            .motsu_expect("should recover signer address");

        assert_eq!(address, alice.address());
    }

    #[motsu::test]
    fn ecrecover_with_invalid_input(
        contract: Contract<PrecompileAccessor>,
        alice: Account,
    ) {
        let to_b256 = |input: &str| {
            Keccak256::new().update(input.as_bytes()).finalize().into()
        };
        let msg_hash = to_b256("Message to sign here.");
        let r = to_b256("1");
        let s = to_b256("1");

        // verify invalid inputs still work
        let address = contract
            .sender(alice)
            .get_signer_address(msg_hash, 27, r, s)
            .motsu_expect("should recover signer address");

        assert_eq!(address, Address::ZERO);
    }
}
