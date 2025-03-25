//! Ethereum Precompiles
use revm_precompile::{secp256k1::ec_recover_run, PrecompileErrors};
use stylus_sdk::{alloy_sol_types::sol, call::MethodError, prelude::*};

sol! {
    /// out of gas is the main error. Others are here just for completeness
    #[derive(Debug)]
    error PrecompileOutOfGas();
    // Blake2 errors
    #[derive(Debug)]
    error PrecompileBlake2WrongLength();
    #[derive(Debug)]
    error PrecompileBlake2WrongFinalIndicatorFlag();
    // Modexp errors
    #[derive(Debug)]
    error PrecompileModexpExpOverflow();
    #[derive(Debug)]
    error PrecompileModexpBaseOverflow();
    #[derive(Debug)]
    error PrecompileModexpModOverflow();
    // Bn128 errors
    #[derive(Debug)]
    error PrecompileBn128FieldPointNotAMember();
    #[derive(Debug)]
    error PrecompileBn128AffineGFailedToCreate();
    #[derive(Debug)]
    error PrecompileBn128PairLength();
    // Blob errors
    /// The input length is not exactly 192 bytes.
    #[derive(Debug)]
    error PrecompileBlobInvalidInputLength();
    /// The commitment does not match the versioned hash.
    #[derive(Debug)]
    error PrecompileBlobMismatchedVersion();
    /// The proof verification failed.
    #[derive(Debug)]
    error PrecompileBlobVerifyKzgProofFailed();
    /// Catch-all variant for other errors.
    #[derive(Debug)]
    error PrecompileOther(string);
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
