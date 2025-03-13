//! Unit-testing context for Stylus contracts.

use core::fmt::Debug;
use std::{
    cell::Cell,
    collections::HashMap,
    hash::Hash,
    ops::{Deref, DerefMut},
    ptr, slice,
    thread::ThreadId,
};

use alloy_primitives::{Address, Bytes, LogData, B256, U256};
use alloy_sol_types::{SolEvent, Word};
use dashmap::{mapref::one::RefMut, DashMap};
use once_cell::sync::Lazy;
use stylus_sdk::{
    host::{WasmVM, VM},
    keccak_const::Keccak256,
    prelude::StorageType,
    ArbResult,
};

use crate::{
    router::{VMRouter, VMRouterContext},
    storage_access::AccessStorage,
};

/// Motsu VM Storage.
///
/// A global mutable key-value store that allows concurrent access.
///
/// The key is the test [`VMContext`], an id of the test thread.
///
/// The value is the [`VMContextStorage`], a storage of the test case.
///
/// NOTE: The [`VMContext::storage`] will panic on lock, when the same key is
/// accessed twice from the same thread.
static MOTSU_VM: Lazy<DashMap<VMContext, VMContextStorage>> =
    Lazy::new(DashMap::new);

/// Context of Motsu test VM associated with the current test thread.
#[allow(clippy::module_name_repetitions)]
#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct VMContext {
    thread_id: ThreadId,
}

impl VMContext {
    /// Get test context associated with the current test thread.
    #[must_use]
    pub fn current() -> Self {
        Self { thread_id: std::thread::current().id() }
    }

    /// Get the raw value at `key` in storage and write it to `value`.
    pub(crate) unsafe fn get_bytes_raw(self, key: *const u8, value: *mut u8) {
        let key = read_bytes32(key);

        write_bytes32(value, self.get_bytes(&key));
    }

    /// Get the value at `key` in storage.
    fn get_bytes(self, key: &Bytes32) -> Bytes32 {
        let storage = self.storage();
        let contract_address =
            storage.contract_address.expect("contract_address should be set");
        storage
            .persistent
            .contracts
            .get(&contract_address)
            .expect("contract receiver should have a storage initialised")
            .data
            .get(key)
            .copied()
            .unwrap_or_default()
    }

    /// Set the raw value at `key` in storage to `value`.
    pub(crate) unsafe fn set_bytes_raw(self, key: *const u8, value: *const u8) {
        let (key, value) = (read_bytes32(key), read_bytes32(value));
        self.set_bytes(key, value);
    }

    /// Set the value at `key` in storage to `value`.
    fn set_bytes(self, key: Bytes32, value: Bytes32) {
        let mut storage = self.storage();
        let contract_address =
            storage.contract_address.expect("contract_address should be set");
        storage
            .persistent
            .contracts
            .get_mut(&contract_address)
            .expect("contract receiver should have a storage initialised")
            .data
            .insert(key, value);
    }

    /// Set the message sender address and return the previous sender if any.
    fn replace_msg_sender(self, msg_sender: Address) -> Option<Address> {
        self.storage().msg_sender.replace(msg_sender)
    }

    /// Get the message sender address.
    #[must_use]
    pub(crate) fn msg_sender(self) -> Option<Address> {
        self.storage().msg_sender
    }

    /// Replace the address of the contract, and return the previous address if
    /// any.
    fn replace_contract_address(self, address: Address) -> Option<Address> {
        self.storage().contract_address.replace(address)
    }

    /// Replace an optional message with `value` and return the previous value
    /// if any.
    ///
    /// Setting `value` to `None` will effectively clear the message value, e.g.
    /// for non "payable" call.
    pub(crate) fn replace_optional_msg_value(
        self,
        value: Option<U256>,
    ) -> Option<U256> {
        std::mem::replace(&mut self.storage().msg_value, value)
    }

    /// Write the value sent to the contract to `output`.
    pub(crate) unsafe fn msg_value_raw(self, output: *mut u8) {
        let value: U256 = self.msg_value().unwrap_or_default();
        write_u256(output, value);
    }

    /// Get the value sent to the contract as [`U256`].
    pub(crate) fn msg_value(self) -> Option<U256> {
        self.storage().msg_value
    }

    /// Get the address of the contract that is called.
    pub(crate) fn contract_address(self) -> Option<Address> {
        self.storage().contract_address
    }

    /// Initialise contract's storage for the current test thread and
    /// `contract_address`.
    fn init_storage<ST: StorageType + VMRouter + 'static>(
        self,
        contract_address: Address,
    ) {
        if MOTSU_VM
            .entry(self)
            .or_default()
            .persistent
            .contracts
            .insert(contract_address, ContractStorage::default())
            .is_some()
        {
            panic!("contract storage already initialized for contract_address `{contract_address}`");
        }

        self.router(contract_address).init_storage::<ST>();
    }

    /// Reset storage for the current [`VMContext`] and `contract_address`.
    ///
    /// If all test contracts are removed, flush storage for the current
    /// test [`VMContext`].
    fn reset_storage(self, contract_address: Address) {
        let mut storage = self.storage();
        storage.persistent.contracts.remove(&contract_address);

        // if no more contracts left,
        if storage.persistent.contracts.is_empty() {
            // drop guard to a concurrent hash map to avoid a panic on lock,
            drop(storage);
            // and erase the test context.
            _ = MOTSU_VM.remove(&self);
        }

        self.router(contract_address).reset_storage();
    }

    /// Call the contract at raw `address` with the given raw `calldata`.
    pub(crate) unsafe fn call_contract_raw(
        self,
        address: *const u8,
        calldata: *const u8,
        calldata_len: usize,
        return_data_size: *mut usize,
    ) -> u8 {
        let address = read_address(address);
        let (selector, input) = decode_calldata(calldata, calldata_len);

        let result = self.call_contract(address, selector, &input, None);
        self.process_arb_result_raw(result, return_data_size)
    }

    /// Call the contract at raw `address` with the given raw `calldata` and
    /// `value`.
    pub(crate) unsafe fn call_contract_with_value_raw(
        self,
        address: *const u8,
        calldata: *const u8,
        calldata_len: usize,
        value: *const u8,
        return_data_size: *mut usize,
    ) -> u8 {
        let address = read_address(address);
        let value = read_u256(value);
        let (selector, input) = decode_calldata(calldata, calldata_len);

        let result = self.call_contract(address, selector, &input, Some(value));
        self.process_arb_result_raw(result, return_data_size)
    }

    /// Based on `result`, set the return data.
    /// Return 0 if `result` is `Ok`, otherwise 1.
    unsafe fn process_arb_result_raw(
        self,
        result: ArbResult,
        return_data_size: *mut usize,
    ) -> u8 {
        match result {
            Ok(res) => {
                return_data_size.write(res.len());
                self.set_return_data(res);
                0
            }
            Err(err) => {
                return_data_size.write(err.len());
                self.set_return_data(err);
                1
            }
        }
    }

    /// Call the function associated with the given `selector` at the given
    /// `contract_address`. Pass `input` and optional `value` to it.
    fn call_contract(
        self,
        contract_address: Address,
        selector: u32,
        input: &[u8],
        value: Option<U256>,
    ) -> ArbResult {
        // Set the caller contract as message sender and callee contract as
        // a receiver (`contract_address`).
        let previous_contract_address = self
            .replace_contract_address(contract_address)
            .expect("contract_address should be set");
        let previous_msg_sender = self
            .replace_msg_sender(previous_contract_address)
            .expect("msg_sender should be set");

        // Set new msg_value, and store the previous one.
        let previous_msg_value = self.replace_optional_msg_value(value);

        // We should do backup before transferring value, to have balances
        // reverted in case of failure.
        let backup = self.storage().persistent.backup_into();

        // Transfer value sent by message sender.
        self.transfer_value();

        // Call external contract.
        let result = self
            .router(contract_address)
            .route(selector, input)
            .unwrap_or_else(|| {
                panic!("selector not found - selector is {selector}")
            });

        // If the call was unsuccessful, we should restore the data.
        if result.is_err() {
            self.storage().persistent.restore_from(backup);
        }

        // Set the previous message sender and contract address back.
        _ = self.replace_contract_address(previous_contract_address);
        _ = self.replace_msg_sender(previous_msg_sender);

        // Set the previous msg_value.
        self.replace_optional_msg_value(previous_msg_value);

        result
    }

    /// Set return data as bytes.
    fn set_return_data(self, data: Vec<u8>) {
        let mut call_storage = self.storage();
        _ = call_storage.return_data_size.insert(data.len());
        _ = call_storage.return_data.insert(data);
    }

    /// Read the return data (with a given `size`) from the last contract call
    /// to the `dest` pointer.
    pub(crate) unsafe fn read_return_data_raw(
        self,
        dest: *mut u8,
        size: usize,
    ) -> usize {
        let data = self.return_data();
        ptr::copy(data.as_ptr(), dest, size);
        data.len().min(size)
    }

    /// Return data's size in bytes from the last contract call.
    pub(crate) fn return_data_size(self) -> usize {
        self.storage()
            .return_data_size
            .take()
            .expect("call_output_len should be set")
    }

    /// Return data's bytes from the last contract call.
    fn return_data(self) -> Vec<u8> {
        self.storage().return_data.take().expect("call_output should be set")
    }

    /// Check if the contract at raw `address` has code.
    pub(crate) unsafe fn has_code_raw(self, address: *const u8) -> bool {
        let address = read_address(address);
        self.has_code(address)
    }

    /// Check if the contract at `address` has code.
    #[must_use]
    fn has_code(self, address: Address) -> bool {
        self.router(address).exists()
    }

    /// Check if the `event` was emitted, by the contract at `address`.
    pub(crate) fn emitted_for<E: SolEvent>(
        self,
        address: &Address,
        event: &E,
    ) -> bool {
        let log_data = event.encode_log_data();

        self.storage()
            .persistent
            .contracts
            .get(address)
            .is_some_and(|contract| contract.events.contains(&log_data))
    }

    /// Get all events of type [`E`] emitted by the contract at `address`.
    pub(crate) fn matching_events_for<E: SolEvent>(
        self,
        address: &Address,
    ) -> Vec<E> {
        self.storage()
            .persistent
            .contracts
            .get(address)
            .map(|contract| {
                contract
                    .events
                    .iter()
                    .filter_map(|log| E::decode_log_data(log, true).ok())
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Store the raw event log `data`, `len` and `topics` number in the
    /// storage.
    pub(crate) unsafe fn store_log_raw(
        self,
        data: *const u8,
        len: usize,
        topics: usize,
    ) {
        let data = slice::from_raw_parts(data, len);
        self.store_log(data, topics);
    }

    /// Store the event log `data` and `topics_number` in the storage.
    fn store_log(self, data: &[u8], topics_number: usize) {
        let topics: Vec<_> = data
            .chunks(Word::len_bytes())
            .map(Word::from_slice)
            .take(topics_number)
            .collect();

        let data_start = Word::len_bytes() * topics_number;
        let data = Bytes::copy_from_slice(&data[data_start..]);

        let log_data =
            LogData::new(topics, data).expect("should create new LogData");

        let mut storage = self.storage();
        let contract_address =
            storage.contract_address.expect("contract_address should be set");
        storage
            .persistent
            .contracts
            .get_mut(&contract_address)
            .expect("contract should have a storage initialised")
            .events
            .push(log_data);
    }

    /// Get the balance of account at `address`.
    pub(crate) fn balance(self, address: Address) -> U256 {
        self.storage()
            .persistent
            .balances
            .get(&address)
            .copied()
            .unwrap_or_default()
    }

    /// Transfer value from the message sender to the contract.
    /// No-op if `msg_sender`, `contract_address` or `msg_value` weren't set.
    ///
    /// # Panics
    ///
    /// * If there is not enough funds to transfer.
    fn transfer_value(self) {
        let storage = self.storage();
        let Some(msg_sender) = storage.msg_sender else {
            return;
        };
        let Some(contract_address) = storage.contract_address else {
            return;
        };
        let Some(msg_value) = storage.msg_value else {
            return;
        };

        // Drop storage to avoid a panic on lock.
        drop(storage);

        // Transfer and panic if there is not enough funds.
        self.transfer(msg_sender, contract_address, msg_value);
    }

    /// Transfer `value` from `from` account to `to` account.
    ///
    /// # Panics
    ///
    /// * If there is not enough funds to transfer.
    fn transfer(self, from: Address, to: Address, value: U256) {
        if value.is_zero() {
            return;
        }

        // Transfer and panic if there is not enough funds.
        self.checked_transfer(from, to, value)
            .unwrap_or_else(|| panic!("{from} account should have enough funds to transfer {value} value"));
    }

    /// Transfer `value` from `from` account to `to` account.
    ///
    /// Returns `None` if there is not enough funds to transfer.
    fn checked_transfer(
        self,
        from: Address,
        to: Address,
        value: U256,
    ) -> Option<()> {
        self.checked_sub_assign_balance(from, value)?;
        self.add_assign_balance(to, value);
        Some(())
    }

    /// Subtract `value` from the balance of `address` account.
    ///
    /// Returns `None` if there is not enough of funds.
    fn checked_sub_assign_balance(
        self,
        address: Address,
        value: U256,
    ) -> Option<U256> {
        let mut storage = self.storage();
        let balance = storage.persistent.balances.entry(address).or_default();
        if *balance < value {
            return None;
        }
        *balance -= value;
        Some(*balance)
    }

    /// Add `value` to the balance of `address` account.
    fn add_assign_balance(self, address: Address, value: U256) -> U256 {
        *self
            .storage()
            .persistent
            .balances
            .entry(address)
            .and_modify(|v| *v += value)
            .or_insert(value)
    }

    /// Reset persistent data backup.
    /// Used when transaction was successful.
    pub(crate) fn reset_backup(self) {
        self.storage().persistent.reset_backup();
    }

    /// Restore persistent data from backup.
    /// Used when transaction failed.
    pub(crate) fn restore_from_backup(self) {
        self.storage().persistent.restore_from_backup();
    }

    /// Create persistent storage backup.
    /// Used when transaction starts.
    fn backup(self) {
        self.storage().persistent.backup();
    }

    /// Set string `tag` for `address`.
    fn set_tag(self, address: Address, tag: String) {
        MOTSU_VM.entry(self).or_default().tags.insert(address, tag);
    }

    /// Replaces non-checksumed addresses in the `msg` with corresponding tags
    /// (if any).
    pub(crate) fn replace_with_tags(self, mut msg: String) -> String {
        let storage = self.storage();
        for (address, tag) in &storage.tags {
            // We need debug formatting, since it reveals non-checksumed
            // address.
            let address = format!("{address:?}");
            msg = msg.replace(&address, tag);
        }
        msg
    }

    /// Get reference to the storage for the current test thread.
    fn storage(self) -> RefMut<'static, VMContext, VMContextStorage> {
        MOTSU_VM.access_storage(&self)
    }

    /// Get router for the contract at `address`.
    fn router(self, address: Address) -> VMRouterContext {
        VMRouterContext::new(self.thread_id, address)
    }

    /// Get the current chain ID.
    pub(crate) fn chain_id(self) -> u64 {
        self.storage().chain_id
    }

    /// Set the chain ID.
    pub fn set_chain_id(self, chain_id: u64) {
        let mut storage = self.storage();
        storage.chain_id = chain_id;
    }
}

/// Read the word from location pointed by `ptr`.
pub(crate) unsafe fn read_bytes32(ptr: *const u8) -> Bytes32 {
    let mut res = Bytes32::default();
    ptr::copy(ptr, res.as_mut_ptr(), WORD_BYTES);
    res
}

/// Write the word `bytes` to the location pointed by `ptr`.
pub(crate) unsafe fn write_bytes32(ptr: *mut u8, bytes: Bytes32) {
    ptr::copy(bytes.as_ptr(), ptr, WORD_BYTES);
}

/// Read the [`Address`] from the raw pointer.
pub(crate) unsafe fn read_address(ptr: *const u8) -> Address {
    let address_bytes = slice::from_raw_parts(ptr, 20);
    Address::from_slice(address_bytes)
}

/// Write the [`Address`] `address` to the location pointed by `ptr`.
pub(crate) unsafe fn write_address(ptr: *mut u8, address: Address) {
    ptr::copy(address.as_ptr(), ptr, 20);
}

/// Read the [`U256`] from the raw pointer.
pub(crate) unsafe fn read_u256(ptr: *const u8) -> U256 {
    let mut data = B256::ZERO;
    ptr::copy(ptr, data.as_mut_ptr(), 32);
    data.into()
}

/// Write the [`U256`] `value` to the location pointed by `ptr`.
pub(crate) unsafe fn write_u256(ptr: *mut u8, value: U256) {
    let bytes: B256 = value.into();
    ptr::copy(bytes.as_ptr(), ptr, 32);
}

/// Decode the selector as [`u32`], and function input as [`Vec<u8>`] from the
/// raw pointer.
unsafe fn decode_calldata(
    calldata: *const u8,
    calldata_len: usize,
) -> (u32, Vec<u8>) {
    let calldata = slice::from_raw_parts(calldata, calldata_len);
    let selector =
        u32::from_be_bytes(TryInto::try_into(&calldata[..4]).unwrap());
    let input = calldata[4..].to_vec();
    (selector, input)
}

/// Main storage for Motsu test VM.
struct VMContextStorage {
    /// Address of the message sender.
    msg_sender: Option<Address>,
    /// The ETH value in wei sent to the program.
    msg_value: Option<U256>,
    /// Address of the contract that is currently receiving the message.
    contract_address: Option<Address>,
    // Output of a contract call.
    return_data: Option<Vec<u8>>,
    // Output length of a contract call.
    return_data_size: Option<usize>,
    /// Persistent storage for Motsu test VM.
    persistent: Backuped<PersistentStorage>,
    /// Account's address to tag mapping.
    tags: HashMap<Address, String>,
    /// Chain ID of the current network.
    chain_id: u64,
}

impl Default for VMContextStorage {
    fn default() -> Self {
        Self {
            msg_sender: None,
            msg_value: None,
            contract_address: None,
            return_data: None,
            return_data_size: None,
            persistent: Backuped::default(),
            tags: HashMap::default(),
            chain_id: 42161, // Arbitrum One chain ID
        }
    }
}

/// Persistent storage for Motsu test VM.
#[derive(Default, Clone)]
struct PersistentStorage {
    /// Contract's address to [`ContractStorage`] mapping.
    contracts: HashMap<Address, ContractStorage>,
    /// Account's address to balance [`U256`] mapping.
    balances: HashMap<Address, U256>,
}

/// Contract's account storage.
#[derive(Default, Clone)]
struct ContractStorage {
    /// Contract's byte storage
    data: ContractData,
    /// Event logs emitted by the contract.
    events: Vec<LogData>,
}

/// Contract's byte storage
type ContractData = HashMap<Bytes32, Bytes32>;
pub(crate) const WORD_BYTES: usize = 32;
pub(crate) type Bytes32 = [u8; WORD_BYTES];

/// A wrapper that allows to back up and restore data.
/// Used for transaction revert.
#[derive(Default)]
struct Backuped<D: Clone + Default> {
    data: D,
    backup: Option<D>,
}

impl<D: Clone + Default> Deref for Backuped<D> {
    type Target = D;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<D: Clone + Default> DerefMut for Backuped<D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<D: Clone + Default> Backuped<D> {
    /// Return data for backup.
    /// Should be used before starting external call between contracts.
    fn backup_into(&self) -> D {
        self.data.clone()
    }

    /// Remove backup data.
    /// Should be used when transaction was successful.
    fn reset_backup(&mut self) {
        _ = self.backup.take();
    }

    /// Restore data from backup removing backup.
    /// Should be used when transaction failed.
    fn restore_from_backup(&mut self) {
        // "Backuped" type `T` can be a more expensive type like a `HashMap`.
        // So instead of cloning it right after transaction, we just pass
        // ownership to the `data` field.
        // For the last transaction (in a test case) we will have less `clone()`
        // invocations, therefore fewer allocations.
        self.data = self.backup.take().expect("unable revert transaction");
    }

    /// Restore data from provided `backup`.
    /// Should be used when external call between contracts failed, to restore
    /// from `backup` persisted on the callstack.
    fn restore_from(&mut self, backup: D) {
        self.data = backup;
    }

    /// Backup data inside `self`.
    /// Should be used when we start a new transaction.
    fn backup(&mut self) {
        let _ = self.backup.insert(self.backup_into());
    }
}

/// Contract call entity, related to the contract type `ST` and the caller's
/// account.
pub struct ContractCall<'a, ST: StorageType> {
    storage: Cell<ST>,
    msg_sender: Address,
    msg_value: Option<U256>,
    /// We need to hold a reference to [`Contract<ST>`], because
    /// `Contract::<ST>::new().sender(alice)` can accidentally drop
    /// [`Contract<ST>`] and call would fail.
    ///
    /// With `contract_ref` code like: `Contract::<ST>::new().sender(alice)`
    /// will not compile.
    contract_ref: &'a Contract<ST>,
}

impl<ST: StorageType> ContractCall<'_, ST> {
    /// Preset the call parameters.
    fn set_call_params(&self) {
        _ = VMContext::current().replace_optional_msg_value(self.msg_value);
        _ = VMContext::current().replace_msg_sender(self.msg_sender);
        _ = VMContext::current()
            .replace_contract_address(self.contract_ref.address);
    }

    /// Invalidate the storage cache of stylus contract [`StorageType`], by
    /// replacing it with an empty storage struct.
    /// Otherwise, instead of expected values, we can receive
    /// artifacts from the previous invocations.
    fn invalidate_storage_type_cache(&self) {
        self.storage.set(create_default_storage_type());
    }
}

impl<ST: StorageType> Deref for ContractCall<'_, ST> {
    type Target = ST;

    #[inline]
    fn deref(&self) -> &Self::Target {
        VMContext::current().backup();

        // Set parameters for call such as `msg_sender`, `contract_address`,
        // `msg_value`.
        self.set_call_params();

        // Transfer value (if any) from the `msg_sender` to `contract_address`,
        // that was set on the previous step.
        VMContext::current().transfer_value();

        // SAFETY: We don't use `ST` contract type as intended by rust.
        // We don't care about any state it has in any property.
        // But we do care that it should go each time through shim and retrieve
        // the only VALID state.
        // And doesn't retrieve any cached properties.
        self.invalidate_storage_type_cache();
        unsafe { self.storage.as_ptr().as_ref().unwrap() }
    }
}

impl<ST: StorageType> DerefMut for ContractCall<'_, ST> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        VMContext::current().backup();

        // Set parameters for call such as `msg_sender`, `contract_address`,
        // `msg_value`.
        self.set_call_params();

        // Transfer value (if any) from the `msg_sender` to `contract_address`,
        // that was set on the previous step.
        VMContext::current().transfer_value();

        self.invalidate_storage_type_cache();
        self.storage.get_mut()
    }
}

/// Contract deployed in the test environment.
pub struct Contract<ST: StorageType> {
    phantom: ::core::marker::PhantomData<ST>,
    address: Address,
}

impl<ST: StorageType> Drop for Contract<ST> {
    fn drop(&mut self) {
        VMContext::current().reset_storage(self.address);
    }
}

impl<ST: StorageType + VMRouter + 'static> Default for Contract<ST> {
    fn default() -> Self {
        Contract::new_at(Address::default())
    }
}

impl<ST: StorageType + VMRouter + 'static> Contract<ST> {
    /// Create a new contract with default storage on the random address.
    #[must_use]
    pub fn new() -> Self {
        Self::random()
    }

    /// Create a new contract with the given `address`.
    #[must_use]
    pub fn new_at(address: Address) -> Self {
        VMContext::current().init_storage::<ST>(address);

        Self { phantom: ::core::marker::PhantomData, address }
    }

    /// Initialize the contract with an `initializer` function, and on behalf of
    /// the given `account`.
    pub fn init<A: Into<Address>, Output>(
        &self,
        sender: A,
        initializer: impl FnOnce(&mut ST) -> Output,
    ) -> Output {
        initializer(&mut self.sender(sender.into()))
    }

    /// Create a new contract with default storage on the random address.
    #[must_use]
    pub fn random() -> Self {
        Self::new_at(Address::random())
    }

    /// Get contract's test address.
    #[must_use]
    pub fn address(&self) -> Address {
        self.address
    }

    /// Call contract `self` with `account` as a sender.
    #[must_use]
    pub fn sender<A: Into<Address>>(&self, account: A) -> ContractCall<ST> {
        ContractCall {
            storage: Cell::new(create_default_storage_type()),
            msg_sender: account.into(),
            msg_value: None,
            contract_ref: self,
        }
    }

    /// Call contract `self` with `account` as a sender and `value`.
    #[must_use]
    pub fn sender_and_value<A: Into<Address>, V: Into<U256>>(
        &self,
        sender: A,
        value: V,
    ) -> ContractCall<ST> {
        let caller_address = sender.into();
        let value = value.into();

        ContractCall {
            storage: Cell::new(create_default_storage_type()),
            msg_sender: caller_address,
            msg_value: Some(value),
            contract_ref: self,
        }
    }

    /// Check if the `event` was emitted, by the contract `self`.
    pub fn emitted<E: SolEvent>(&self, event: &E) -> bool {
        VMContext::current().emitted_for(&self.address, event)
    }

    /// Assert that the `event` was emitted, by the contract `self`.
    /// In contrast to [`Self::emitted`] event type `E` should implement
    /// [`Debug`].
    ///
    /// # Panics
    ///
    /// * If the event was not emitted, includes all matching emitted events (if
    ///   any) in the error message.
    #[track_caller]
    pub fn assert_emitted<E: SolEvent + Debug>(&self, event: &E) {
        let context = VMContext::current();
        if context.emitted_for(&self.address, event) {
            return;
        }

        let panic_msg = "event was not emitted";
        let matching_events = context.matching_events_for::<E>(&self.address);

        let panic_msg = if matching_events.is_empty() {
            format!("{panic_msg}, no matching events found")
        } else {
            format!("{panic_msg}, matching events: {matching_events:?}")
        };
        let panic_msg = context.replace_with_tags(panic_msg);
        panic!("{}", panic_msg);
    }
}

/// Create a default [`StorageType`] `ST` type with at [`U256::ZERO`] slot and
/// `0` offset.
pub(crate) fn create_default_storage_type<ST: StorageType>() -> ST {
    unsafe { ST::new(U256::ZERO, 0, VM { host: Box::new(WasmVM {}) }) }
}

/// Account used to call contracts.
#[derive(Clone, Copy)]
pub struct Account {
    address: Address,
}

impl From<Account> for Address {
    fn from(value: Account) -> Self {
        value.address
    }
}

impl Account {
    /// Create a new account with the given `address`.
    #[must_use]
    pub const fn new_at(address: Address) -> Self {
        Self { address }
    }

    /// Create a new account with random address.
    #[must_use]
    pub fn random() -> Self {
        Self::new_at(Address::random())
    }

    /// Get account's address.
    #[must_use]
    pub fn address(&self) -> Address {
        self.address
    }
}

/// Fund the account.
pub trait Funding {
    /// Fund the account with the given `value`.
    fn fund(&self, value: U256);

    /// Get the balance of the account.
    fn balance(&self) -> U256;
}

impl Funding for Address {
    fn fund(&self, value: U256) {
        VMContext::current().add_assign_balance(*self, value);
    }

    fn balance(&self) -> U256 {
        VMContext::current().balance(*self)
    }
}

impl Funding for Account {
    fn fund(&self, value: U256) {
        self.address().fund(value);
    }

    fn balance(&self) -> U256 {
        self.address().balance()
    }
}

impl<ST: StorageType + VMRouter + 'static> Funding for Contract<ST> {
    fn fund(&self, value: U256) {
        self.address().fund(value);
    }

    fn balance(&self) -> U256 {
        self.address().balance()
    }
}

/// Deterministically derive from a string representation.
pub trait FromTag {
    /// Deterministically derive inner address of `Self` from a string `tag`.
    fn from_tag(tag: &str) -> Self;
}

impl FromTag for Address {
    fn from_tag(tag: &str) -> Self {
        let hash = Keccak256::new().update(tag.as_bytes()).finalize();
        let address = Address::from_slice(&hash[..20]);
        VMContext::current().set_tag(address, tag.to_string());
        address
    }
}

impl FromTag for Account {
    fn from_tag(tag: &str) -> Self {
        Account::new_at(Address::from_tag(tag))
    }
}

impl<ST: StorageType + VMRouter + 'static> FromTag for Contract<ST> {
    fn from_tag(tag: &str) -> Self {
        Contract::new_at(Address::from_tag(tag))
    }
}
