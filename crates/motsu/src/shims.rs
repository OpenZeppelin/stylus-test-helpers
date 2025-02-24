//! Shims that mock common host imports in Stylus `wasm` programs.
//!
//! Most of the documentation is taken from the [Stylus source].
//!
//! We allow unsafe here because safety is guaranteed by the Stylus team.
//!
//! [Stylus source]: https://github.com/OffchainLabs/stylus/blob/484efac4f56fb70f96d4890748b8ec2543d88acd/arbitrator/wasm-libraries/user-host-trait/src/lib.rs
//!
//! ## Motivation
//!
//! Without these shims, we can't currently run unit tests for stylus contracts,
//! since the symbols the compiled binaries expect to find are not there.
//!
//! If you run `cargo test` on a fresh Stylus project, it will error with:
//!
//! ```terminal
//! dyld[97792]: missing symbol called
//! ```
#![allow(dead_code)]
#![allow(clippy::missing_safety_doc)]
use std::slice;

use tiny_keccak::{Hasher, Keccak};

use crate::context::{
    read_address, write_address, write_bytes32, write_u256, VMContext,
    WORD_BYTES,
};

/// Arbitrum's CHAID ID.
const CHAIN_ID: u64 = 42161;

/// Externally Owned Account (EOA) code hash (wallet account).
const EOA_CODEHASH: &[u8; 66] =
    b"0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470";

/// Contract Account (CA) code hash (smart contract code).
/// NOTE: can be any 256-bit value to pass `has_code` check.
const CA_CODEHASH: &[u8; 66] =
    b"0x1111111111111111111111111111111111111111111111111111111111111111";

/// Efficiently computes the [`keccak256`] hash of the given preimage.
/// The semantics are equivalent to that of the EVM's [`SHA3`] opcode.
///
/// [`keccak256`]: https://en.wikipedia.org/wiki/SHA-3
/// [`SHA3`]: https://www.evm.codes/#20
#[no_mangle]
unsafe extern "C" fn native_keccak256(
    bytes: *const u8,
    len: usize,
    output: *mut u8,
) {
    let mut hasher = Keccak::v256();

    let data = slice::from_raw_parts(bytes, len);
    hasher.update(data);

    let output = slice::from_raw_parts_mut(output, WORD_BYTES);
    hasher.finalize(output);
}

/// Reads a 32-byte value from permanent storage.
///
/// Stylus's storage format is identical to that of the EVM. This means that,
/// under the hood, this hostio is accessing the 32-byte value stored in the EVM
/// state trie at offset `key`, which will be `0` when not previously set. The
/// semantics, then, are equivalent to that of the EVM's [`SLOAD`] opcode.
///
/// [`SLOAD`]: https://www.evm.codes/#54
#[no_mangle]
unsafe extern "C" fn storage_load_bytes32(key: *const u8, out: *mut u8) {
    VMContext::current().get_bytes_raw(key, out);
}

/// Writes a 32-byte value to the permanent storage cache.
///
/// Stylus's storage format is identical to that of the EVM. This means that,
/// under the hood, this hostio represents storing a 32-byte value into the EVM
/// state trie at offset `key`. Refunds are tabulated exactly as in the EVM. The
/// semantics, then, are equivalent to that of the EVM's [`SSTORE`] opcode.
///
/// Note: because the value is cached, one must call `storage_flush_cache` to
/// persist it.
///
/// [`SSTORE`]: https://www.evm.codes/#55
#[no_mangle]
unsafe extern "C" fn storage_cache_bytes32(key: *const u8, value: *const u8) {
    VMContext::current().set_bytes_raw(key, value);
}

/// Persists any dirty values in the storage cache to the EVM state trie,
/// dropping the cache entirely if requested. Analogous to repeated invocations
/// of [`SSTORE`].
///
/// [`SSTORE`]: https://www.evm.codes/#55
#[no_mangle]
unsafe extern "C" fn storage_flush_cache(_: bool) {
    // No-op: we don't use the cache in our unit-tests.
}

/// Gets the address of the account that called the program.
///
/// For normal L2-to-L2 transactions, the semantics are equivalent to that of
/// the EVM's [`CALLER`] opcode, including in cases arising from
/// [`DELEGATE_CALL`].
///
/// For L1-to-L2 retryable ticket transactions, the top-level sender's address
/// will be aliased. See [`Retryable Ticket Address Aliasing`][aliasing] for
/// more information on how this works.
///
/// [`CALLER`]: https://www.evm.codes/#33
/// [`DELEGATE_CALL`]: https://www.evm.codes/#f4
/// [aliasing]: https://developer.arbitrum.io/arbos/l1-to-l2-messaging#address-aliasing
#[no_mangle]
unsafe extern "C" fn msg_sender(sender: *mut u8) {
    let msg_sender =
        VMContext::current().msg_sender().expect("msg_sender should be set");
    write_address(sender, msg_sender);
}

/// Get the ETH value (U256) in wei sent to the program.
#[no_mangle]
unsafe extern "C" fn msg_value(value: *mut u8) {
    VMContext::current().msg_value_raw(value);
}

/// Gets the address of the current program. The semantics are equivalent to
/// that of the EVM's [`ADDRESS`] opcode.
///
/// [`ADDRESS`]: https://www.evm.codes/#30
///
/// # Panics
///
/// * If fails to parse `CONTRACT_ADDRESS` as an address.
#[no_mangle]
unsafe extern "C" fn contract_address(address: *mut u8) {
    let contract_address = VMContext::current()
        .contract_address()
        .expect("contract_address should be set");
    write_address(address, contract_address);
}

/// Gets the chain ID of the current chain. The semantics are equivalent to
/// that of the EVM's [`CHAINID`] opcode.
///
/// [`CHAINID`]: https://www.evm.codes/#46
#[no_mangle]
unsafe extern "C" fn chainid() -> u64 {
    CHAIN_ID
}

/// Emits an EVM log with the given number of topics and data, the first bytes
/// of which should be the 32-byte-aligned topic data.
///
/// The semantics are equivalent to that of the EVM's [`LOG0`], [`LOG1`],
/// [`LOG2`], [`LOG3`], and [`LOG4`] opcodes based on the number of topics
/// specified. Requesting more than `4` topics will induce a revert.
///
/// [`LOG0`]: https://www.evm.codes/#a0
/// [`LOG1`]: https://www.evm.codes/#a1
/// [`LOG2`]: https://www.evm.codes/#a2
/// [`LOG3`]: https://www.evm.codes/#a3
/// [`LOG4`]: https://www.evm.codes/#a4
#[no_mangle]
unsafe extern "C" fn emit_log(data: *const u8, len: usize, topics: usize) {
    VMContext::current().store_log_raw(data, len, topics);
}

/// Gets the code hash of the account at the given address.
///
/// The semantics are equivalent to that of the EVM's [`EXT_CODEHASH`] opcode.
/// Note that the code hash of an account without code will be the empty hash
/// `keccak("") =
///     c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`.
///
/// [`EXT_CODEHASH`]: https://www.evm.codes/#3F
#[no_mangle]
unsafe extern "C" fn account_codehash(address: *const u8, dest: *mut u8) {
    let code_hash = if VMContext::current().has_code_raw(address) {
        CA_CODEHASH
    } else {
        EOA_CODEHASH
    };

    let account_codehash =
        const_hex::const_decode_to_array::<WORD_BYTES>(code_hash).unwrap();

    write_bytes32(dest, account_codehash);
}

/// Gets the ETH balance in wei of the account at the given address.
/// The semantics are equivalent to that of the EVM's [`BALANCE`] opcode.
///
/// [`BALANCE`]: https://www.evm.codes/#31
#[no_mangle]
unsafe extern "C" fn account_balance(address: *const u8, dest: *mut u8) {
    let address = read_address(address);
    let balance = VMContext::current().balance(address);
    write_u256(dest, balance);
}

/// Returns the length of the last EVM call or deployment return result, or `0`
/// if neither has happened during the program's execution.
///
/// The semantics are equivalent to that of the EVM's [`RETURN_DATA_SIZE`]
/// opcode.
///
/// [`RETURN_DATA_SIZE`]: https://www.evm.codes/#3d
#[no_mangle]
unsafe extern "C" fn return_data_size() -> usize {
    VMContext::current().return_data_size()
}

/// Copies the bytes of the last EVM call or deployment return result.
///
/// Does not revert if out of bounds, but rather copies the overlapping portion.
/// The semantics are otherwise equivalent to that of the EVM's
/// [`RETURN_DATA_COPY`] opcode.
///
/// Returns the number of bytes written.
///
/// [`RETURN_DATA_COPY`]: https://www.evm.codes/#3e
#[no_mangle]
unsafe extern "C" fn read_return_data(
    dest: *mut u8,
    _offset: usize,
    size: usize,
) -> usize {
    VMContext::current().read_return_data_raw(dest, size)
}

/// Calls the contract at the given address with options for passing value and
/// to limit the amount of gas supplied. The return status indicates whether the
/// call succeeded and is nonzero on failure.
///
/// In both cases, `return_data_len` will store the length of the result, the
/// bytes of which can be read via the `read_return_data` hostio. The bytes are
/// not returned directly so that the programmer can potentially save gas by
/// choosing which subset of the return result they'd like to copy.
///
/// The semantics are equivalent to that of the EVM's [`CALL`] opcode, including
/// call value stipends and the 63/64 gas rule. This means that supplying the
/// `u64::MAX` gas can be used to send as much as possible.
///
/// [`CALL`]: https://www.evm.codes/#f1
#[no_mangle]
unsafe extern "C" fn call_contract(
    contract: *const u8,
    calldata: *const u8,
    calldata_len: usize,
    value: *const u8,
    _gas: u64,
    return_data_len: *mut usize,
) -> u8 {
    VMContext::current().call_contract_with_value_raw(
        contract,
        calldata,
        calldata_len,
        value,
        return_data_len,
    )
}

/// Static calls the contract at the given address, with the option to limit the
/// amount of gas supplied. The return status indicates whether the call
/// succeeded, and is nonzero on failure.
///
/// In both cases `return_data_len` will store the length of the result, the
/// bytes of which can be read via the `read_return_data` hostio. The bytes are
/// not returned directly so that the programmer can potentially save gas by
/// choosing which subset of the return result they'd like to copy.
///
/// The semantics are equivalent to that of the EVM's [`STATIC_CALL`] opcode,
/// including the 63/64 gas rule. This means that supplying `u64::MAX` gas can
/// be used to send as much as possible.
///
/// [`STATIC_CALL`]: https://www.evm.codes/#FA
#[no_mangle]
unsafe extern "C" fn static_call_contract(
    contract: *const u8,
    calldata: *const u8,
    calldata_len: usize,
    _gas: u64,
    return_data_len: *mut usize,
) -> u8 {
    VMContext::current().call_contract_raw(
        contract,
        calldata,
        calldata_len,
        return_data_len,
    )
}

/// Delegate calls the contract at the given address, with the option to limit
/// the amount of gas supplied. The return status indicates whether the call
/// succeeded and is nonzero on failure.
///
/// In both cases, `return_data_len` will store the length of the result, the
/// bytes of which can be read via the `read_return_data` hostio. The bytes are
/// not returned directly so that the programmer can potentially save gas by
/// choosing which subset of the return result they'd like to copy.
///
/// The semantics are equivalent to that of the EVM's [`DELEGATE_CALL`] opcode,
/// including the 63/64 gas rule. This means that supplying `u64::MAX` gas can
/// be used to send as much as possible.
///
/// [`DELEGATE_CALL`]: https://www.evm.codes/#F4
#[no_mangle]
unsafe extern "C" fn delegate_call_contract(
    contract: *const u8,
    calldata: *const u8,
    calldata_len: usize,
    _gas: u64,
    return_data_len: *mut usize,
) -> u8 {
    VMContext::current().call_contract_raw(
        contract,
        calldata,
        calldata_len,
        return_data_len,
    )
}

/// Gets a bounded estimate of the Unix timestamp at which the Sequencer
/// sequenced the transaction. See [`Block Numbers and Time`] for more
/// information on how this value is determined.
///
/// [`Block Numbers and Time`]: https://developer.arbitrum.io/time
#[no_mangle]
unsafe extern "C" fn block_timestamp() -> u64 {
    // Epoch timestamp: 1st January 2025 00::00::00
    1_735_689_600
}
