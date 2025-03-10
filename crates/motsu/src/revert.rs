//! This module contains transaction revert logic, and it is not triggered by
//! default.
//!
//! To revert a transaction in case of an error result, you should call one of
//! the following functions:
//!
//! - [`ResultExt::motsu_unwrap`]
//! - [`ResultExt::motsu_unwrap_err`]
//! - [`ResultExt::motsu_expect`]
//! - [`ResultExt::motsu_expect_err`]
//! - [`ResultExt::motsu_res`]

use core::fmt;
use std::ops::{Deref, DerefMut};

use crate::context::VMContext;

/// Motsu extension trait for [`Result`].
///
/// Allows transaction reverts and provides call metadata for error messages.
#[allow(clippy::missing_errors_doc)]
pub trait ResultExt<T, E: fmt::Debug> {
    /// Returns contained `Ok` value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// * If the value is `Err`, with a panic message including call metadata.
    fn motsu_unwrap(self) -> T;

    /// Returns contained `Err` value, consuming the `self` value and reverts
    /// transaction.
    ///
    /// # Panics
    ///
    /// * If the value is `Ok`, with a panic message including call metadata.
    fn motsu_unwrap_err(self) -> E;

    /// Returns contained `Ok` value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// * If the value is `Err`, with a panic message including custom `msg` and
    ///   call metadata.
    fn motsu_expect(self, msg: &str) -> T;

    /// Returns contained `Err` value, consuming the `self` value and reverts
    /// transaction.
    ///
    /// # Panics
    ///
    /// * If the value is `Ok`, with a panic message including custom `msg` and
    ///   call metadata.
    fn motsu_expect_err(self, msg: &str) -> E;

    /// Returns `self` [`Result`] and reverts the transaction in case of `Err`
    /// value.
    fn motsu_res(self) -> Result<T, E>;
}

impl<T, E: fmt::Debug> ResultExt<T, E> for Result<T, E> {
    #[track_caller]
    fn motsu_unwrap(self) -> T {
        match self.motsu_res() {
            Ok(value) => value,
            Err(err) => {
                let panic_msg = VMContext::current().panic_msg_with_err(err);
                panic!("{panic_msg}");
            }
        }
    }

    #[track_caller]
    fn motsu_unwrap_err(self) -> E {
        match self.motsu_res() {
            Ok(_value) => {
                let panic_msg = VMContext::current().panic_msg();
                panic!("{panic_msg}");
            }
            Err(err) => err,
        }
    }

    #[track_caller]
    fn motsu_expect(self, msg: &str) -> T {
        match self.motsu_res() {
            Ok(value) => value,
            Err(err) => {
                let panic_msg = VMContext::current().panic_msg_with_err(err);
                panic!("{msg}: {panic_msg}");
            }
        }
    }

    #[track_caller]
    fn motsu_expect_err(self, msg: &str) -> E {
        match self.motsu_res() {
            Ok(_value) => {
                let panic_msg = VMContext::current().panic_msg();
                panic!("{msg}: {panic_msg}");
            }
            Err(err) => err,
        }
    }

    fn motsu_res(self) -> Result<T, E> {
        match self {
            Ok(_) => {
                VMContext::current().reset_backup();
            }
            Err(_) => {
                VMContext::current().restore_from_backup();
            }
        }
        self
    }
}

impl VMContext {
    /// Returns a panic message for calls with expected errors.
    fn panic_msg(self) -> String {
        let msg_sender = self.msg_sender().expect("msg_sender should be set");
        let contract_address =
            self.contract_address().expect("contract_address should be set");

        let panic_msg = format!(
            "account {msg_sender:?} should fail to call {contract_address:?}"
        );

        self.replace_with_tags(panic_msg)
    }

    /// Returns a panic message for calls without expected errors.
    /// Unexpected error `err` will be included into the panic message.
    fn panic_msg_with_err<E: fmt::Debug>(self, err: E) -> String {
        let msg_sender = self.msg_sender().expect("msg_sender should be set");
        let contract_address =
            self.contract_address().expect("contract_address should be set");

        let panic_msg = format!("account {msg_sender:?} failed to call {contract_address:?}: {err:?}");

        self.replace_with_tags(panic_msg)
    }
}

// TODO#q: move to context.rs
/// A wrapper that allows to back up and restore data.
/// Used for transaction revert.
#[derive(Default)]
pub(crate) struct Backuped<D: Clone + Default> {
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
    pub(crate) fn backup_into(&self) -> D {
        self.data.clone()
    }

    /// Remove backup data.
    /// Should be used when transaction was successful.
    pub(crate) fn reset_backup(&mut self) {
        _ = self.backup.take();
    }

    /// Restore data from backup removing backup.
    /// Should be used when transaction failed.
    pub(crate) fn restore_from_backup(&mut self) {
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
    pub(crate) fn restore_from(&mut self, backup: D) {
        self.data = backup;
    }

    /// Backup data inside `self`.
    /// Should be used when we start a new transaction.
    pub(crate) fn backup(&mut self) {
        let _ = self.backup.insert(self.backup_into());
    }
}
