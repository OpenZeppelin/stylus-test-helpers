//! Unit-testing context for Stylus contracts.

use std::{collections::HashMap, ptr, slice, thread::ThreadId};

use alloy_primitives::{Address, U256};
use dashmap::{mapref::one::RefMut, DashMap};
use once_cell::sync::Lazy;
use stylus_sdk::{alloy_primitives::uint, prelude::StorageType, ArbResult};

use crate::{
    prelude::{Bytes32, WORD_BYTES},
    router::{RouterContext, TestRouter},
};

/// Storage mock.
///
/// A global mutable key-value store that allows concurrent access.
///
/// The key is the test [`Context`], an id of the test thread.
///
/// The value is the [`MockStorage`], a storage of the test case.
///
/// NOTE: The [`DashMap`] will deadlock execution, when the same key is
/// accessed twice from the same thread.
static STORAGE: Lazy<DashMap<Context, MockStorage>> = Lazy::new(DashMap::new);

/// Context of stylus unit tests associated with the current test thread.
#[allow(clippy::module_name_repetitions)]
#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct Context {
    thread_id: ThreadId,
}

impl Context {
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
            .contract_data
            .get(&contract_address)
            .expect("contract receiver should have a storage initialised")
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
            .contract_data
            .get_mut(&contract_address)
            .expect("contract receiver should have a storage initialised")
            .insert(key, value);
    }

    /// Set the message sender address.
    fn set_msg_sender(self, msg_sender: Address) -> Option<Address> {
        self.storage().msg_sender.replace(msg_sender)
    }

    /// Get the message sender address.
    #[must_use]
    pub fn msg_sender(self) -> Option<Address> {
        self.storage().msg_sender
    }

    /// Set the address of the contract, that is called.
    fn set_contract_address(self, address: Address) -> Option<Address> {
        self.storage().contract_address.replace(address)
    }

    /// Get the address of the contract, that is called.
    pub(crate) fn contract_address(self) -> Option<Address> {
        self.storage().contract_address
    }

    /// Initialise contract's storage for the current test thread and
    /// `contract_address`.
    fn init_storage<ST: StorageType + TestRouter + 'static>(
        self,
        contract_address: Address,
    ) {
        if STORAGE
            .entry(self)
            .or_default()
            .contract_data
            .insert(contract_address, HashMap::new())
            .is_some()
        {
            panic!("contract storage already initialized for contract_address `{contract_address}`");
        }

        self.router(contract_address).init_storage::<ST>();
    }

    /// Reset storage for the current [`Context`] and `contract_address`.
    ///
    /// If all test contracts are removed, flush storage for the current
    /// test [`Context`].
    fn reset_storage(self, contract_address: Address) {
        let mut storage = self.storage();
        storage.contract_data.remove(&contract_address);

        // if no more contracts left,
        if storage.contract_data.is_empty() {
            // drop guard to a concurrent hash map to avoid a deadlock,
            drop(storage);
            // and erase the test context.
            let _ = STORAGE.remove(&self);
        }

        self.router(contract_address).reset_storage();
    }

    /// Call the contract at raw `address` with the given raw `calldata`.
    pub(crate) unsafe fn call_contract_raw(
        self,
        address: *const u8,
        calldata: *const u8,
        calldata_len: usize,
        return_data_len: *mut usize,
    ) -> u8 {
        let address = decode_address(address);
        let (selector, input) = decode_calldata(calldata, calldata_len);

        let result = self.call_contract(address, selector, &input);
        self.process_arb_result_raw(result, return_data_len)
    }

    /// Call the contract at raw `address` with the given raw `calldata` and
    /// `value`.
    pub(crate) unsafe fn call_contract_with_value_raw(
        self,
        address: *const u8,
        calldata: *const u8,
        calldata_len: usize,
        value: *const u8,
        return_data_len: *mut usize,
    ) -> u8 {
        let address = decode_address(address);
        let value = decode_u256(value);
        let (selector, input) = decode_calldata(calldata, calldata_len);

        let result =
            self.call_contract_with_value(address, selector, &input, value);
        self.process_arb_result_raw(result, return_data_len)
    }

    /// Based on `result`, set the return data.
    /// Return 0 if `result` is `Ok`, otherwise return 1.
    unsafe fn process_arb_result_raw(
        self,
        result: ArbResult,
        return_data_len: *mut usize,
    ) -> u8 {
        match result {
            Ok(res) => {
                return_data_len.write(res.len());
                self.set_return_data(res);
                0
            }
            Err(err) => {
                return_data_len.write(err.len());
                self.set_return_data(err);
                1
            }
        }
    }

    /// Call the function associated with the given `selector` at the given
    /// `contract_address`. Pass `input` and `value` to it.
    fn call_contract_with_value(
        self,
        contract_address: Address,
        selector: u32,
        input: &[u8],
        value: U256,
    ) -> ArbResult {
        // Set new msg_value, and store the previous one.
        let previous_msg_value = self.set_msg_value(value);

        let result = self.call_contract(contract_address, selector, input);

        // Set the previous msg_value if there is any.
        if let Some(previous) = previous_msg_value {
            let _ = self.set_msg_value(previous);
        }

        result
    }

    /// Call the function associated with the given `selector` at the given
    /// `contract_address`. Pass `input` to it.
    fn call_contract(
        self,
        contract_address: Address,
        selector: u32,
        input: &[u8],
    ) -> ArbResult {
        // Set the caller contract as message sender and callee contract as
        // a receiver (`contract_address`).
        let previous_contract_address = self
            .set_contract_address(contract_address)
            .expect("contract_address should be set");
        let previous_msg_sender = self
            .set_msg_sender(previous_contract_address)
            .expect("msg_sender should be set");

        // Call external contract.
        let result = self
            .router(contract_address)
            .route(selector, input)
            .unwrap_or_else(|| {
                panic!("selector not found - selector is {selector}")
            });

        // Set the previous message sender and contract address back.
        let _ = self.set_contract_address(previous_contract_address);
        let _ = self.set_msg_sender(previous_msg_sender);

        result
    }

    /// Set return data as bytes.
    fn set_return_data(self, data: Vec<u8>) {
        let mut call_storage = self.storage();
        let _ = call_storage.call_output_len.insert(data.len());
        let _ = call_storage.call_output.insert(data);
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
        data.len()
    }

    /// Return data's size in bytes from the last contract call.
    pub(crate) fn return_data_size(self) -> usize {
        self.storage()
            .call_output_len
            .take()
            .expect("call_output_len should be set")
    }

    /// Return data's bytes from the last contract call.
    fn return_data(self) -> Vec<u8> {
        self.storage().call_output.take().expect("call_output should be set")
    }

    /// Check if the contract at raw `address` has code.
    pub(crate) unsafe fn has_code_raw(self, address: *const u8) -> bool {
        let address = decode_address(address);
        self.has_code(address)
    }

    /// Check if the contract at `address` has code.
    #[must_use]
    fn has_code(self, address: Address) -> bool {
        self.router(address).exists()
    }

    pub(crate) unsafe fn balance_raw(self, address: *const u8) -> U256 {
        // TODO#q: write to destination here
        let address = decode_address(address);
        self.balance(address)
    }

    fn balance(self, address: Address) -> U256 {
        self.storage().balances.get(&address).copied().unwrap_or_default()
    }

    pub(crate) fn set_msg_value(self, value: U256) -> Option<U256> {
        self.storage().msg_value.replace(value)
    }

    /// Write the value sent to the contract to `output`.
    pub(crate) unsafe fn msg_value_raw(self, output: *mut u8) {
        let value: U256 = self.msg_value();
        std::ptr::copy(value.as_le_slice().as_ptr(), output, 32);
    }

    /// Get the value sent to the contract as [`U256`].
    pub(crate) fn msg_value(self) -> U256 {
        self.storage().msg_value.unwrap_or_default()
    }

    fn transfer_funds_from_caller(self) {
        let sender = self.msg_sender().expect("msg_sender should be set");
        let value = self.msg_value();
        self.add_assign_balance(sender, value);
    }

    fn checked_transfer(
        self,
        from: Address,
        to: Address,
        value: U256,
    ) -> Option<()> {
        let _ = self.checked_sub_assign_balance(from, value)?;
        self.add_assign_balance(to, value);
        Some(())
    }

    fn checked_sub_assign_balance(
        self,
        address: Address,
        value: U256,
    ) -> Option<U256> {
        let mut storage = self.storage();
        let balance = storage.balances.entry(address).or_default();
        if *balance < value {
            return None;
        }
        *balance -= value;
        Some(*balance)
    }

    fn add_assign_balance(self, address: Address, value: U256) -> U256 {
        *self
            .storage()
            .balances
            .entry(address)
            .and_modify(|v| *v += value)
            .or_insert(value)
    }

    /// Get reference to the storage for the current test thread.
    fn storage(self) -> RefMut<'static, Context, MockStorage> {
        STORAGE.get_mut(&self).expect("contract should be initialised first")
    }

    /// Get router for the contract at `address`.
    fn router(self, address: Address) -> RouterContext {
        RouterContext::new(self.thread_id, address)
    }
}

/// Read the word from location pointed by `ptr`.
unsafe fn read_bytes32(ptr: *const u8) -> Bytes32 {
    let mut res = Bytes32::default();
    ptr::copy(ptr, res.as_mut_ptr(), WORD_BYTES);
    res
}

/// Write the word `bytes` to the location pointed by `ptr`.
unsafe fn write_bytes32(ptr: *mut u8, bytes: Bytes32) {
    ptr::copy(bytes.as_ptr(), ptr, WORD_BYTES);
}

/// Decode the [`Address`] from the raw pointer.
unsafe fn decode_address(ptr: *const u8) -> Address {
    let address_bytes = slice::from_raw_parts(ptr, 20);
    Address::from_slice(address_bytes)
}

/// Decode the [`U256`] from the raw pointer.
unsafe fn decode_u256(ptr: *const u8) -> U256 {
    let address_bytes = slice::from_raw_parts(ptr, 32);
    U256::from_le_slice(address_bytes)
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

/// Storage for unit test's mock data.
#[derive(Default)]
struct MockStorage {
    /// Address of the message sender.
    msg_sender: Option<Address>,
    /// The ETH value in wei sent to the program.
    msg_value: Option<U256>,
    /// Address of the contract that is currently receiving the message.
    contract_address: Option<Address>,
    /// Contract's address to mock data storage mapping.
    contract_data: HashMap<Address, ContractStorage>,
    /// Account's address to balance mapping.
    balances: HashMap<Address, U256>,
    // Output of a contract call.
    call_output: Option<Vec<u8>>,
    // Output length of a contract call.
    call_output_len: Option<usize>,
}

type ContractStorage = HashMap<Bytes32, Bytes32>;

/// Contract call entity, related to the contract type `ST` and the caller's
/// account.
pub struct ContractCall<'a, ST: StorageType> {
    storage: ST,
    caller_address: Address,
    value: Option<U256>,
    /// We need to hold a reference to [`Contract<ST>`], because
    /// `Contract::<ST>::new().sender(alice)` can accidentally drop
    /// [`Contract<ST>`].
    ///
    /// With `contract_ref` code like: `Contract::<ST>::new().sender(alice)`
    /// will not compile.
    contract_ref: &'a Contract<ST>,
}

impl<ST: StorageType> ContractCall<'_, ST> {
    /// Get the contract's address.
    pub fn address(&self) -> Address {
        self.contract_ref.address
    }

    /// Preset the call parameters.
    fn set_call_params(&self) {
        if let Some(value) = self.value {
            let _ = Context::current().set_msg_value(value);
        }
        let _ = Context::current().set_msg_sender(self.caller_address);
        let _ = Context::current().set_contract_address(self.address());
    }
}

impl<ST: StorageType> ::core::ops::Deref for ContractCall<'_, ST> {
    type Target = ST;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.set_call_params();
        &self.storage
    }
}

impl<ST: StorageType> ::core::ops::DerefMut for ContractCall<'_, ST> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.set_call_params();
        &mut self.storage
    }
}

/// Contract deployed in the test environment.
pub struct Contract<ST: StorageType> {
    phantom: ::core::marker::PhantomData<ST>,
    address: Address,
}

impl<ST: StorageType> Drop for Contract<ST> {
    fn drop(&mut self) {
        Context::current().reset_storage(self.address);
    }
}

impl<ST: StorageType + TestRouter + 'static> Default for Contract<ST> {
    fn default() -> Self {
        Contract::new_at(Address::default())
    }
}

impl<ST: StorageType + TestRouter + 'static> Contract<ST> {
    /// Create a new contract with default storage on the random address.
    #[must_use]
    pub fn new() -> Self {
        Self::random()
    }

    /// Create a new contract with the given `address`.
    #[must_use]
    pub fn new_at(address: Address) -> Self {
        Context::current().init_storage::<ST>(address);

        Self { phantom: ::core::marker::PhantomData, address }
    }

    /// Initialize the contract with an `initializer` function, and on behalf of
    /// the given `account`.
    pub fn init<A: Into<Address>, Output>(
        &self,
        account: A,
        initializer: impl FnOnce(&mut ST) -> Output,
    ) -> Output {
        initializer(&mut self.sender(account.into()))
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
            storage: unsafe { ST::new(uint!(0_U256), 0) },
            caller_address: account.into(),
            value: None,
            contract_ref: self,
        }
    }

    /// Call contract `self` with `account` as a sender and `value`.
    #[must_use]
    pub fn sender_and_value<A: Into<Address>, V: Into<U256>>(
        &self,
        account: A,
        value: V,
    ) -> ContractCall<ST> {
        ContractCall {
            storage: unsafe { ST::new(uint!(0_U256), 0) },
            caller_address: account.into(),
            value: Some(value.into()),
            contract_ref: self,
        }
    }
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

    /// Get account's balance.
    #[must_use]
    pub fn balance(&self) -> U256 {
        Context::current().balance(self.address)
    }
}
