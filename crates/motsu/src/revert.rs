// TODO#q: add docs (optimistic behaviour)

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
    /// * if the value is `Err`, with a panic message including call metadata.
    fn motsu_unwrap(self) -> T;

    /// Returns contained `Err` value, consuming the `self` value and reverts
    /// transaction.
    ///
    /// # Panics
    ///
    /// * if the value is `Ok`, with a panic message including call metadata.
    fn motsu_unwrap_err(self) -> E;

    /// Returns contained `Ok` value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// * if the value is `Err`, with a panic message including custom `msg` and
    ///   call metadata.
    fn motsu_expect(self, msg: &str) -> T;

    /// Returns contained `Err` value, consuming the `self` value and reverts
    /// transaction.
    ///
    /// # Panics
    /// * if the value is `Ok`, with a panic message including custom `msg` and
    ///   call metadata.
    fn motsu_expect_err(self, msg: &str) -> E;

    /// Returns `self` without any changes and reverts transaction in case of
    /// `Err` value.
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
    /// Should be used before starting external call between contracts.
    pub(crate) fn clone_data(&self) -> D {
        self.data.clone()
    }

    /// Should be used when transaction was successful.
    pub(crate) fn reset_backup(&mut self) {
        _ = self.backup.take();
    }

    /// Should be used when transaction failed.
    pub(crate) fn restore_from_backup(&mut self) {
        self.data = self.backup.take().expect("unable revert transaction");
    }

    /// Should be used when external call between contracts failed, to restore
    /// from `backup` persisted on the callstack.
    pub(crate) fn restore_from(&mut self, backup: D) {
        self.data = backup;
    }

    /// Should be used when we start a new transaction.
    pub(crate) fn create_backup(&mut self) {
        let _ = self.backup.insert(self.data.clone());
    }
}
