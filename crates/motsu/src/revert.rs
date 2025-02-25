// TODO#q: add docs (optimistic behaviour)

use core::fmt;
use std::ops::{Deref, DerefMut};

use crate::context::VMContext;

// TODO#q: document ResultExt

pub trait ResultExt<T, E: fmt::Debug> {
    fn motsu_unwrap(self) -> T;
    fn motsu_unwrap_err(self) -> E;
    fn motsu_expect(self, msg: &str) -> T;
    fn motsu_expect_err(self, msg: &str) -> E;
    // TODO#q: motsu_res(self)
}

// TODO#q: Don't print debug information about the error.
// `E` should implement `Into<Vec<u8>>`

impl<T, E: fmt::Debug> ResultExt<T, E> for Result<T, E> {
    #[track_caller]
    fn motsu_unwrap(self) -> T {
        match self {
            Ok(value) => {
                VMContext::current().reset_backup();
                value
            }
            Err(err) => {
                // TODO#q: unify with motsu_expect
                let context = VMContext::current();
                let msg_sender =
                    context.msg_sender().expect("msg_sender should be set");
                let contract_address = context
                    .contract_address()
                    .expect("contract_address should be set");

                let panic_msg = format!("account {msg_sender:?} failed to call {contract_address:?}: {err:?}");

                let panic_msg = context.replace_with_tags(panic_msg);
                panic!("{panic_msg}");
            }
        }
    }

    #[track_caller]
    fn motsu_unwrap_err(self) -> E {
        match self {
            Ok(_value) => {
                // TODO#q: unify with motsu_expect_err
                let context = VMContext::current();
                let msg_sender =
                    context.msg_sender().expect("msg_sender should be set");
                let contract_address = context
                    .contract_address()
                    .expect("contract_address should be set");

                let panic_msg = format!("account {msg_sender:?} should fail to call {contract_address:?}");

                let panic_msg = context.replace_with_tags(panic_msg);
                panic!("{panic_msg}");
            }
            Err(err) => {
                VMContext::current().restore_from_backup();
                err
            }
        }
    }

    #[track_caller]
    fn motsu_expect(self, msg: &str) -> T {
        match self {
            Ok(value) => {
                VMContext::current().reset_backup();
                value
            }
            Err(err) => {
                let context = VMContext::current();
                let msg_sender =
                    context.msg_sender().expect("msg_sender should be set");
                let contract_address = context
                    .contract_address()
                    .expect("contract_address should be set");

                let panic_msg = format!("account {msg_sender:?} failed to call {contract_address:?}: {err:?}");

                let panic_msg = context.replace_with_tags(panic_msg);
                panic!("{msg}: {panic_msg}");
            }
        }
    }

    #[track_caller]
    fn motsu_expect_err(self, msg: &str) -> E {
        match self {
            Ok(_value) => {
                let context = VMContext::current();
                let msg_sender =
                    context.msg_sender().expect("msg_sender should be set");
                let contract_address = context
                    .contract_address()
                    .expect("contract_address should be set");

                let panic_msg = format!("account {msg_sender:?} should fail to call {contract_address:?}");

                let panic_msg = context.replace_with_tags(panic_msg);
                panic!("{msg}: {panic_msg}");
            }
            Err(err) => {
                VMContext::current().restore_from_backup();
                err
            }
        }
    }
}

// TODO#q: document `Backuped`

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
