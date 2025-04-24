//! Stylus-compatible error wrappers for [`PrecompileErrors`].
use revm_precompile::PrecompileErrors;
use stylus_sdk::{alloy_sol_types::sol, call::MethodError, prelude::*};

sol! {
    /// Out of gas is the main error. Others are here just for completeness.
    #[derive(Debug)]
    error PrecompileOutOfGas();
    /// Blake2 wrong length.
    #[derive(Debug)]
    error PrecompileBlake2WrongLength();
    /// Blake2 wrong indicator flag.
    #[derive(Debug)]
    error PrecompileBlake2WrongFinalIndicatorFlag();
    /// Modexp exponent overflow.
    #[derive(Debug)]
    error PrecompileModexpExpOverflow();
    /// Modexp base overflow.
    #[derive(Debug)]
    error PrecompileModexpBaseOverflow();
    /// Modexp mod overflow.
    #[derive(Debug)]
    error PrecompileModexpModOverflow();
    /// Bn128 field point not a member.
    #[derive(Debug)]
    error PrecompileBn128FieldPointNotAMember();
    /// Bn128 affine G failed to create.
    #[derive(Debug)]
    error PrecompileBn128AffineGFailedToCreate();
    /// Bn128 pair length error.
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
    /// Fatal.
    #[derive(Debug)]
    error PrecompileFatal(string msg);
}

#[derive(SolidityError, Debug)]
pub enum Error {
    /// Out of gas is the main error. Others are here just for completeness.
    OutOfGas(PrecompileOutOfGas),
    /// Blake2 wrong length.
    Blake2WrongLength(PrecompileBlake2WrongLength),
    /// Blake2 wrong indicator flag.
    Blake2WrongFinalIndicatorFlag(PrecompileBlake2WrongFinalIndicatorFlag),
    /// Modexp exponent overflow.
    ModexpExpOverflow(PrecompileModexpExpOverflow),
    /// Modexp base overflow.
    ModexpBaseOverflow(PrecompileModexpBaseOverflow),
    /// Modexp mod overflow.
    ModexpModOverflow(PrecompileModexpModOverflow),
    /// Bn128 field point not a member.
    Bn128FieldPointNotAMember(PrecompileBn128FieldPointNotAMember),
    /// Bn128 affine G failed to create.
    Bn128AffineGFailedToCreate(PrecompileBn128AffineGFailedToCreate),
    /// Bn128 pair length error.
    Bn128PairLength(PrecompileBn128PairLength),
    /// The blob input length is not exactly 192 bytes.
    BlobInvalidInputLength(PrecompileBlobInvalidInputLength),
    /// The blob commitment does not match the versioned hash.
    BlobMismatchedVersion(PrecompileBlobMismatchedVersion),
    /// The blob proof verification failed.
    BlobVerifyKzgProofFailed(PrecompileBlobVerifyKzgProofFailed),
    /// Catch-all variant for other errors.
    Other(PrecompileOther),
    /// Fatal.
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
