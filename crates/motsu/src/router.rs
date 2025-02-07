//! Router context for external calls mocks.

use std::{
    borrow::BorrowMut,
    marker::PhantomData,
    sync::{Arc, Mutex},
    thread::ThreadId,
};

use alloy_primitives::{uint, Address};
use dashmap::{mapref::one::RefMut, DashMap};
use once_cell::sync::Lazy;
use stylus_sdk::{
    abi::Router,
    prelude::{StorageType, TopLevelStorage},
    ArbResult,
};

use crate::storage_access::AccessStorage;

/// Motsu VM Router Storage.
///
/// A global mutable key-value store that allows concurrent access.
///
/// The key is the [`VMRouterContext`], a combination of [`ThreadId`] and
/// [`Address`] to avoid a panic on lock, while calling more than two contracts
/// consecutive.
///
/// The value is the [`VMRouterStorage`], a router of the contract generated by
/// `stylus-sdk`.
///
/// NOTE: The [`VMRouterContext::storage`] will panic on lock, when the same key
/// is accessed twice from the same thread.
static MOTSU_VM_ROUTERS: Lazy<DashMap<VMRouterContext, VMRouterStorage>> =
    Lazy::new(DashMap::new);

/// Context of Motsu test VM router associated with the current test thread and
/// contract's address.
#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub(crate) struct VMRouterContext {
    thread_id: ThreadId,
    contract_address: Address,
}

impl VMRouterContext {
    /// Create a new router context.
    pub(crate) fn new(thread: ThreadId, contract_address: Address) -> Self {
        Self { thread_id: thread, contract_address }
    }

    /// Get reference to the call storage for the current test thread.
    fn storage(self) -> RefMut<'static, VMRouterContext, VMRouterStorage> {
        MOTSU_VM_ROUTERS.access_storage(&self)
    }

    /// Check if the router exists for the contract.
    pub(crate) fn exists(self) -> bool {
        MOTSU_VM_ROUTERS.contains_key(&self)
    }

    pub(crate) fn route(
        self,
        selector: u32,
        input: &[u8],
    ) -> Option<ArbResult> {
        let storage = self.storage();
        let router = Arc::clone(&storage.router);

        // Drop the storage reference to avoid a panic on lock.
        drop(storage);

        router.create_and_route(selector, input)
    }

    /// Initialise contract router for the current test thread and
    /// `contract_address`.
    pub(crate) fn init_storage<ST: StorageType + VMRouter + 'static>(self) {
        let contract_address = self.contract_address;
        if MOTSU_VM_ROUTERS
            .insert(
                self,
                VMRouterStorage {
                    // Mutex is important since a contract type is not `Sync`.
                    // We don't lock anything and let rust compiler know that
                    // `RouterFactory` is `Sync` and can be shared between
                    // threads.
                    router: Arc::new(RouterFactory::<Mutex<ST>> {
                        _phantom: PhantomData,
                    }),
                },
            )
            .is_some()
        {
            panic!("contract's router is already initialized - contract_address is {contract_address}");
        }
    }

    /// Reset router storage for the current [`VMRouterContext`].
    pub(crate) fn reset_storage(self) {
        MOTSU_VM_ROUTERS.remove(&self);
    }
}

/// Metadata related to the router of an external contract.
struct VMRouterStorage {
    // Contract's router.
    router: Arc<dyn CreateRouter>,
}

/// A trait for router's creation.
trait CreateRouter: Send + Sync {
    /// Instantiate a new router.
    fn create(&self) -> Box<dyn VMRouter>;

    /// Instantiate a new router and instantly route a message to the matching
    /// selector.
    /// Returns `None` if the `selector` wasn't found.
    fn create_and_route(
        &self,
        selector: u32,
        input: &[u8],
    ) -> Option<ArbResult> {
        self.create().route(selector, input)
    }
}

/// A factory for router creation.
struct RouterFactory<R> {
    _phantom: PhantomData<R>,
}

impl<R: StorageType + VMRouter + 'static> CreateRouter
    for RouterFactory<Mutex<R>>
{
    fn create(&self) -> Box<dyn VMRouter> {
        Box::new(unsafe { R::new(uint!(0_U256), 0) })
    }
}

/// A trait for routing messages to the matching selector.
#[allow(clippy::module_name_repetitions)]
pub trait VMRouter: Send {
    /// Tries to find and execute a method for the given `selector`, returning
    /// `None` if the `selector` wasn't found.
    fn route(&mut self, selector: u32, input: &[u8]) -> Option<ArbResult>;
}

impl<R> VMRouter for R
where
    R: Router<R> + TopLevelStorage + BorrowMut<R::Storage> + Send,
{
    fn route(&mut self, selector: u32, input: &[u8]) -> Option<ArbResult> {
        <Self as Router<R>>::route(self, selector, input)
    }
}
