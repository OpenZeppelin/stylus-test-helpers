use std::{borrow::BorrowMut, sync::Mutex, thread::ThreadId};

use alloy_primitives::{uint, Address};
use dashmap::{mapref::one::RefMut, DashMap};
use once_cell::sync::Lazy;
use stylus_sdk::{
    abi::Router,
    prelude::{StorageType, TopLevelStorage},
    ArbResult,
};

/// Context for the router of a test contract for current test thread and
/// contract's address.
pub(crate) struct RouterContext {
    thread: std::thread::Thread,
    contract_address: Address,
}

impl RouterContext {
    /// Create a new router context.
    pub(crate) fn new(
        thread: std::thread::Thread,
        contract_address: Address,
    ) -> Self {
        Self { thread, contract_address }
    }

    /// Get reference to the call storage for the current test thread.
    fn storage(&self) -> RefMut<'static, RouterStorageKey, RouterStorage> {
        ROUTER_STORAGE
            .get_mut(&self.storage_key())
            .expect("contract should be initialised first")
    }

    /// Check if the router exists for the contract.
    pub(crate) fn exists(&self) -> bool {
        ROUTER_STORAGE.contains_key(&self.storage_key())
    }

    fn storage_key(&self) -> RouterStorageKey {
        (self.thread.id(), self.contract_address)
    }

    pub(crate) fn route(
        &self,
        selector: u32,
        input: &[u8],
    ) -> Option<ArbResult> {
        let router = &self.storage().router;
        let mut router = router.lock().expect("should lock test router");
        router.route(selector, input)
    }

    /// Initialise contract router for the current test thread and
    /// `contract_address`.
    pub(crate) fn init_storage<ST: StorageType + TestRouter + 'static>(self) {
        let storage_key = self.storage_key();
        let contract_address = self.contract_address;
        if ROUTER_STORAGE
            .insert(
                storage_key,
                RouterStorage {
                    router: Mutex::new(Box::new(unsafe {
                        ST::new(uint!(0_U256), 0)
                    })),
                },
            )
            .is_some()
        {
            panic!("contract's router is already initialized - contract_address is {contract_address}");
        }
    }
}

type RouterStorageKey = (ThreadId, Address);

/// The key is the name of the test thread, and the value is contract's router
/// data.
static ROUTER_STORAGE: Lazy<DashMap<RouterStorageKey, RouterStorage>> =
    Lazy::new(DashMap::new);

/// Metadata related to the router of an external contract.
struct RouterStorage {
    // Contract's router.
    // NOTE: Mutex is important since contract type is not `Sync`.
    router: Mutex<Box<dyn TestRouter>>,
}

/// A trait for routing messages to the appropriate selector in tests.
pub(crate) trait TestRouter: Send {
    /// Tries to find and execute a method for the given selector, returning
    /// `None` if none is found.
    fn route(&mut self, selector: u32, input: &[u8]) -> Option<ArbResult>;
}

impl<R> TestRouter for R
where
    R: Router<R> + TopLevelStorage + BorrowMut<R::Storage> + Send,
{
    fn route(&mut self, selector: u32, input: &[u8]) -> Option<ArbResult> {
        <Self as Router<R>>::route(self, selector, input)
    }
}
