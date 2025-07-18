//! Tooling for accessing Motsu test VM storage.

use std::hash::Hash;

use dashmap::{mapref::one::RefMut, try_result::TryResult, DashMap};

/// Trait for Motsu test VM storage access.
pub(crate) trait AccessStorage {
    type Key;
    type Value;

    /// Get mutable access to storage with `key`.
    ///
    /// # Panics
    ///
    /// * After 10 attempts to access the storage.
    /// * If the contract wasn't initialized.
    fn access_storage(
        &self,
        key: &Self::Key,
    ) -> RefMut<'_, Self::Key, Self::Value> {
        self.access_storage_with_backoff(key, 10)
    }

    /// Get mutable access to storage with `key`, with `backoff` number of
    /// attempts.
    ///
    /// # Panics
    ///
    /// * After `backoff` attempts to access the storage.
    /// * If the contract wasn't initialized.
    fn access_storage_with_backoff(
        &self,
        key: &Self::Key,
        backoff: u32,
    ) -> RefMut<'_, Self::Key, Self::Value>;
}

impl<K: Hash + Eq, V> AccessStorage for DashMap<K, V> {
    type Key = K;
    type Value = V;

    fn access_storage_with_backoff(
        &self,
        key: &Self::Key,
        backoff: u32,
    ) -> RefMut<'_, Self::Key, Self::Value> {
        {
            match self.try_get_mut(key) {
                TryResult::Present(router) => router,
                TryResult::Absent => {
                    panic!("contract should be initialised first")
                }
                TryResult::Locked => {
                    if backoff == 0 {
                        panic!("storage is locked")
                    } else {
                        std::thread::sleep(std::time::Duration::from_millis(1));
                        self.access_storage_with_backoff(key, backoff - 1)
                    }
                }
            }
        }
    }
}
