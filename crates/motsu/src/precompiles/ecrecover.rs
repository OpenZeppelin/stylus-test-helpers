//! EcRecover Contract simulating that is deployed on the chain to simulate the
//! being precompiled.
use revm_precompile::{
    secp256k1::{ec_recover_run, ECRECOVER},
    PrecompileErrors,
};
use stylus_sdk::{
    alloy_primitives::Address, alloy_sol_types::sol, call::MethodError,
    prelude::*,
};

pub(crate) const ADDRESS: Address = ECRECOVER.0;

sol! {
    /// out of gas is the main error. Others are here just for completeness
    #[derive(Debug)]
    error PrecompileOutOfGas();
    // Blake2 wrong length
    #[derive(Debug)]
    error PrecompileBlake2WrongLength();
    // Blake2 wrong indicator flag
    #[derive(Debug)]
    error PrecompileBlake2WrongFinalIndicatorFlag();
    // Modexp exponent overflow
    #[derive(Debug)]
    error PrecompileModexpExpOverflow();
    // Modexp base overflow
    #[derive(Debug)]
    error PrecompileModexpBaseOverflow();
    // Modexp mod overflow
    #[derive(Debug)]
    error PrecompileModexpModOverflow();
    // Bn128 field point not a member
    #[derive(Debug)]
    error PrecompileBn128FieldPointNotAMember();
    // Bn128 affine G failed to create
    #[derive(Debug)]
    error PrecompileBn128AffineGFailedToCreate();
    // Bn128 pair length error
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
    OutOfGas(PrecompileOutOfGas),
    Blake2WrongLength(PrecompileBlake2WrongLength),
    Blake2WrongFinalIndicatorFlag(PrecompileBlake2WrongFinalIndicatorFlag),
    ModexpExpOverflow(PrecompileModexpExpOverflow),
    ModexpBaseOverflow(PrecompileModexpBaseOverflow),
    ModexpModOverflow(PrecompileModexpModOverflow),
    Bn128FieldPointNotAMember(PrecompileBn128FieldPointNotAMember),
    Bn128AffineGFailedToCreate(PrecompileBn128AffineGFailedToCreate),
    Bn128PairLength(PrecompileBn128PairLength),
    BlobInvalidInputLength(PrecompileBlobInvalidInputLength),
    BlobMismatchedVersion(PrecompileBlobMismatchedVersion),
    BlobVerifyKzgProofFailed(PrecompileBlobVerifyKzgProofFailed),
    Other(PrecompileOther),
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
    #[fallback]
    fn fallback(&self) -> Result<Vec<u8>, Vec<u8>> {
        let args = vec![];
        let b = &(args.into());
        let r: Result<Vec<u8>, Error> =
            ec_recover_run(b, 3_000) // TODO: update to self.vm().evm_gas_left() after transitioning
                // to Host trait
                .map(|out| out.bytes.into())
                .map_err(|e| e.into());
        r.map_err(|e| e.into())
    }
}

#[cfg(test)]
mod tests {
    use alloy_signer::SignerSync;
    use motsu::precompiles::ecrecover;
    use stylus_sdk::{
        alloy_primitives::{Address, B256},
        alloy_sol_types::{sol, SolValue},
        call::{self, Call},
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
        let message = "Message to sign here.".as_bytes();

        // get v, r and s values
        let signature = alice.signer().sign_message_sync(message).unwrap();
        let recid: u8 = signature.recid().into();
        let (v, r, s) = (
            // ecrecover expects `v` to be in the range {27,28}
            recid + 27,
            signature.r().into(),
            signature.s().into(),
        );

        let address = contract
            .sender(alice)
            .get_signer_address(B256::from_slice(message), v, r, s)
            .unwrap();

        assert_eq!(address, alice.address());
    }

    #[motsu::test]
    fn ecrecover_with_invalid_input(
        contract: Contract<PrecompileAccessor>,
        alice: Account,
    ) {
        let message = "Message to sign here.".as_bytes();

        // verify invalid inputs still work
        let address = contract
            .sender(alice)
            .get_signer_address(
                B256::from_slice(message),
                27,
                B256::from_slice(&[1]),
                B256::from_slice(&[1]),
            )
            .unwrap();

        assert_eq!(address, Address::ZERO);
    }
}
