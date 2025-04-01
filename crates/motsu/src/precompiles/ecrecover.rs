//! Contract simulating the precompiled `ecrecover` contract on-chain.
use alloy_primitives::Bytes;
use revm_precompile::{
    secp256k1::{ec_recover_run, ECRECOVER},
    PrecompileErrors, PrecompileOutput,
};
use stylus_sdk::{
    alloy_primitives::Address, alloy_sol_types::sol, call::MethodError, evm,
    prelude::*,
};

pub(crate) const ADDRESS: Address = ECRECOVER.0;

sol! {
    /// Out of gas is the main error. Others are here just for completeness
    #[derive(Debug)]
    error PrecompileOutOfGas();
    /// Blake2 wrong length
    #[derive(Debug)]
    error PrecompileBlake2WrongLength();
    /// Blake2 wrong indicator flag
    #[derive(Debug)]
    error PrecompileBlake2WrongFinalIndicatorFlag();
    /// Modexp exponent overflow
    #[derive(Debug)]
    error PrecompileModexpExpOverflow();
    /// Modexp base overflow
    #[derive(Debug)]
    error PrecompileModexpBaseOverflow();
    /// Modexp mod overflow
    #[derive(Debug)]
    error PrecompileModexpModOverflow();
    /// Bn128 field point not a member
    #[derive(Debug)]
    error PrecompileBn128FieldPointNotAMember();
    /// Bn128 affine G failed to create
    #[derive(Debug)]
    error PrecompileBn128AffineGFailedToCreate();
    /// Bn128 pair length error
    #[derive(Debug)]
    error PrecompileBn128PairLength();
    /// The blob input length is not exactly 192 bytes.
    #[derive(Debug)]
    error PrecompileBlobInvalidInputLength();
    /// The blob commitment does not match the versioned hash.
    #[derive(Debug)]
    error PrecompileBlobMismatchedVersion();
    /// The blob proof verification failed.
    #[derive(Debug)]
    error PrecompileBlobVerifyKzgProofFailed();
    /// Catch-all variant for other errors.
    #[derive(Debug)]
    error PrecompileOther(string);
    /// Fatal
    #[derive(Debug)]
    error PrecompileFatal(string msg);
}

#[derive(SolidityError, Debug)]
pub enum Error {
    /// Out of gas is the main error. Others are here just for completeness
    OutOfGas(PrecompileOutOfGas),
    /// Blake2 wrong length
    Blake2WrongLength(PrecompileBlake2WrongLength),
    /// Blake2 wrong indicator flag
    Blake2WrongFinalIndicatorFlag(PrecompileBlake2WrongFinalIndicatorFlag),
    /// Modexp exponent overflow
    ModexpExpOverflow(PrecompileModexpExpOverflow),
    /// Modexp base overflow
    ModexpBaseOverflow(PrecompileModexpBaseOverflow),
    /// Modexp mod overflow
    ModexpModOverflow(PrecompileModexpModOverflow),
    /// Bn128 field point not a member
    Bn128FieldPointNotAMember(PrecompileBn128FieldPointNotAMember),
    /// Bn128 affine G failed to create
    Bn128AffineGFailedToCreate(PrecompileBn128AffineGFailedToCreate),
    /// Bn128 pair length error
    Bn128PairLength(PrecompileBn128PairLength),
    /// The blob input length is not exactly 192 bytes.
    BlobInvalidInputLength(PrecompileBlobInvalidInputLength),
    /// The blob commitment does not match the versioned hash.
    BlobMismatchedVersion(PrecompileBlobMismatchedVersion),
    /// The blob proof verification failed.
    BlobVerifyKzgProofFailed(PrecompileBlobVerifyKzgProofFailed),
    /// Catch-all variant for other errors.
    Other(PrecompileOther),
    /// Fatal
    Fatal(PrecompileFatal),
}

impl core::convert::From<PrecompileErrors> for Error {
    fn from(value: PrecompileErrors) -> Self {
        match value {
            PrecompileErrors::Error(nested) => match nested {
                revm_precompile::Error::OutOfGas => {
                    Error::OutOfGas(PrecompileOutOfGas {})
                }
                revm_precompile::Error::Blake2WrongLength => {
                    Error::Blake2WrongLength(PrecompileBlake2WrongLength {})
                }
                revm_precompile::Error::Blake2WrongFinalIndicatorFlag => {
                    Error::Blake2WrongFinalIndicatorFlag(
                        PrecompileBlake2WrongFinalIndicatorFlag {},
                    )
                }
                revm_precompile::Error::ModexpExpOverflow => {
                    Error::ModexpExpOverflow(PrecompileModexpExpOverflow {})
                }
                revm_precompile::Error::ModexpBaseOverflow => {
                    Error::ModexpBaseOverflow(PrecompileModexpBaseOverflow {})
                }
                revm_precompile::Error::ModexpModOverflow => {
                    Error::ModexpModOverflow(PrecompileModexpModOverflow {})
                }
                revm_precompile::Error::Bn128FieldPointNotAMember => {
                    Error::Bn128FieldPointNotAMember(
                        PrecompileBn128FieldPointNotAMember {},
                    )
                }
                revm_precompile::Error::Bn128AffineGFailedToCreate => {
                    Error::Bn128AffineGFailedToCreate(
                        PrecompileBn128AffineGFailedToCreate {},
                    )
                }
                revm_precompile::Error::Bn128PairLength => {
                    Error::Bn128PairLength(PrecompileBn128PairLength {})
                }
                revm_precompile::Error::BlobInvalidInputLength => {
                    Error::BlobInvalidInputLength(
                        PrecompileBlobInvalidInputLength {},
                    )
                }
                revm_precompile::Error::BlobMismatchedVersion => {
                    Error::BlobMismatchedVersion(
                        PrecompileBlobMismatchedVersion {},
                    )
                }
                revm_precompile::Error::BlobVerifyKzgProofFailed => {
                    Error::BlobVerifyKzgProofFailed(
                        PrecompileBlobVerifyKzgProofFailed {},
                    )
                }
                revm_precompile::Error::Other(msg) => {
                    Error::Other(PrecompileOther { _0: msg })
                }
            },
            PrecompileErrors::Fatal { msg } => {
                Error::Fatal(PrecompileFatal { msg })
            }
        }
    }
}

impl MethodError for Error {
    fn encode(self) -> Vec<u8> {
        self.into()
    }
}

/// EcRecover Contract.
#[storage]
pub struct EcRecover;

unsafe impl TopLevelStorage for EcRecover {}

#[public]
impl EcRecover {
    /// Fallback function.
    #[fallback]
    fn fallback(&self, calldata: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        ec_recover_run(&Bytes::copy_from_slice(calldata), evm::gas_left())
            .map(output_to_left_padded_vec)
            .map_err(Into::<Error>::into)
            .map_err(Into::into)
    }
}

/// Converts Bytes to a Vec<u8> with left-padding to ensure it's 32 bytes.
///
/// Assumes the input Bytes will never be more than 32 bytes.
/// If the input Bytes is less than 32 bytes, the result will be left-padded
/// with zeroes.
///
/// # Arguments
///
/// * `bytes` - The Bytes to convert (must be ≤ 32 bytes)
///
/// # Returns
///
/// A Vec<u8> containing exactly 32 bytes
fn output_to_left_padded_vec(out: PrecompileOutput) -> Vec<u8> {
    let mut result = vec![0u8; 32];

    // Calculate the starting index in the result vector (for left padding)
    let start_index = 32 - out.bytes.len();

    result[start_index..].copy_from_slice(&out.bytes[..]);

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
