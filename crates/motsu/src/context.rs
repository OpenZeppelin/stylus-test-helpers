//! Unit-testing context for Stylus contracts.

use std::{collections::HashMap, ptr, slice, thread::ThreadId};

use alloy_primitives::Address;
use dashmap::{mapref::one::RefMut, DashMap};
use once_cell::sync::Lazy;
use stylus_sdk::{alloy_primitives::uint, prelude::StorageType, ArbResult};

use crate::{
    prelude::{Bytes32, WORD_BYTES},
    router::{RouterContext, TestRouter},
};

/// Storage mock: A global mutable key-value store.
/// Allows concurrent access.
///
/// The key is the test [`Context`], an id of the test thread.
///
/// The value is the [`MockStorage`], a storage of the test case.
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

    /// Set the message sender account address.
    fn set_msg_sender(self, msg_sender: Address) -> Option<Address> {
        self.storage().msg_sender.replace(msg_sender)
    }

    /// Get the message sender account address.
    #[must_use]
    pub fn get_msg_sender(self) -> Option<Address> {
        self.storage().msg_sender
    }

    /// Set the address of the contract, that is called.
    fn set_contract_address(self, address: Address) -> Option<Address> {
        self.storage().contract_address.replace(address)
    }

    /// Get the address of the contract, that is called.
    pub(crate) fn get_contract_address(self) -> Option<Address> {
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
        let address_bytes = slice::from_raw_parts(address, 20);
        let address = Address::from_slice(address_bytes);

        let input = slice::from_raw_parts(calldata, calldata_len);
        let selector =
            u32::from_be_bytes(TryInto::try_into(&input[..4]).unwrap());

        match self.call_contract(address, selector, &input[4..]) {
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

    /// Call the function associated with the given `selector` and pass `input`
    /// to it, at the given `contract_address`.
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
        let data = self.get_return_data();
        ptr::copy(data.as_ptr(), dest, size);
        data.len()
    }

    /// Get return data's size in bytes.
    pub(crate) fn get_return_data_size(self) -> usize {
        self.storage()
            .call_output_len
            .take()
            .expect("call_output_len should be set")
    }

    /// Get return data's bytes.
    fn get_return_data(self) -> Vec<u8> {
        self.storage().call_output.take().expect("call_output should be set")
    }

    /// Check if the contract at raw `address` has code.
    pub(crate) unsafe fn has_code_raw(self, address: *const u8) -> bool {
        let address_bytes = slice::from_raw_parts(address, 20);
        let address = Address::from_slice(address_bytes);
        self.has_code(address)
    }

    /// Check if the contract at `address` has code.
    #[must_use]
    fn has_code(self, address: Address) -> bool {
        self.router(address).exists()
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

/// Storage for unit test's mock data.
#[derive(Default)]
struct MockStorage {
    /// Address of the message sender.
    msg_sender: Option<Address>,
    /// Address of the contract that is currently receiving the message.
    contract_address: Option<Address>,
    /// Contract's address to mock data storage mapping.
    contract_data: HashMap<Address, ContractStorage>,
    // Output of a contract call.
    call_output: Option<Vec<u8>>,
    // Output length of a contract call.
    call_output_len: Option<usize>,
}

type ContractStorage = HashMap<Bytes32, Bytes32>;

/// Contract call entity, related to the contract type `ST` and the caller's
/// account.
pub struct ContractCall<ST: StorageType> {
    contract: ST,
    caller_address: Address,
    contract_address: Address,
}

impl<ST: StorageType> ContractCall<ST> {
    /// Get the contract's address.
    pub fn address(&self) -> Address {
        self.contract_address
    }

    /// Preset the call parameters.
    fn set_call_params(&self) {
        let _ = Context::current().set_msg_sender(self.caller_address);
        let _ = Context::current().set_contract_address(self.contract_address);
    }
}

impl<ST: StorageType> ::core::ops::Deref for ContractCall<ST> {
    type Target = ST;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.set_call_params();
        &self.contract
    }
}

impl<ST: StorageType> ::core::ops::DerefMut for ContractCall<ST> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.set_call_params();
        &mut self.contract
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
        Contract::random()
    }
}

impl<ST: StorageType + TestRouter + 'static> Contract<ST> {
    /// Create a new contract with the given `address`.
    #[must_use]
    pub fn new(address: Address) -> Self {
        Context::current().init_storage::<ST>(address);

        Self { phantom: ::core::marker::PhantomData, address }
    }

    /// Initialize the contract with an `initializer` function, and on behalf of
    /// the given `account`.
    pub fn init<A: Into<Address>>(
        &self,
        account: A,
        initializer: impl FnOnce(&mut ST),
    ) {
        initializer(&mut self.sender(account.into()));
    }

    /// Create a new contract with random address.
    #[must_use]
    pub fn random() -> Self {
        Self::new(Address::random())
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
            contract: unsafe { ST::new(uint!(0_U256), 0) },
            caller_address: account.into(),
            contract_address: self.address,
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
    pub const fn new(address: Address) -> Self {
        Self { address }
    }

    /// Create a new account with random address.
    #[must_use]
    pub fn random() -> Self {
        Self::new(Address::random())
    }

    /// Get account's address.
    #[must_use]
    pub fn address(&self) -> Address {
        self.address
    }
}
