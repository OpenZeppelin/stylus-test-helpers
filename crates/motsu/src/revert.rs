// TODO#q: add docs

use core::fmt;

pub trait ResultExt<T, E: fmt::Debug> {
    fn motsu_unwrap(self) -> T;
    fn motsu_unwrap_err(self) -> E;
    fn motsu_expect(self, msg: &str) -> T;
    fn motsu_expect_err(self, msg: &str) -> E;
}

// TODO#q: substitute tags in the error message
// TODO#q: revert transaction when it is applicable

impl<T: fmt::Debug, E: fmt::Debug> ResultExt<T, E> for Result<T, E> {
    #[track_caller]
    fn motsu_unwrap(self) -> T {
        match self {
            Ok(value) => value,
            Err(err) => panic!(
                "called `Result::motsu_unwrap()` on an `Err` value: {:?}",
                err
            ),
        }
    }

    #[track_caller]
    fn motsu_unwrap_err(self) -> E {
        match self {
            Ok(value) => panic!(
                "called `Result::motsu_unwrap_err()` on an `Ok` value: {:?}",
                value
            ),
            Err(err) => err,
        }
    }

    #[track_caller]
    fn motsu_expect(self, msg: &str) -> T {
        match self {
            Ok(value) => value,
            Err(err) => panic!("{}", msg),
        }
    }

    #[track_caller]
    fn motsu_expect_err(self, msg: &str) -> E {
        match self {
            Ok(value) => panic!("{}", msg),
            Err(err) => err,
        }
    }
}

#[derive(Default)]
pub(crate) struct Backuped<D: Clone + Default> {
    data: D,
    // TODO#q: do we need an optional backup?
    backup: Option<D>,
}

impl<D: Clone + Default> Backuped<D> {
    fn new(data: D) -> Self {
        Self { data: data.clone(), backup: Some(data) }
    }

    // TODO#q: implement deref?
    fn data(&self) -> &D {
        &self.data
    }

    fn data_mut(&mut self) -> &mut D {
        &mut self.data
    }

    // Should be called before starting call between contracts.
    fn clone_data(&self) -> D {
        self.data.clone()
    }

    /// Should be called when transaction was successful.
    fn reset_backup(&mut self) {
        // To not copy backup another time.
        _ = self.backup.take();
    }

    /// Should be called when transaction failed.
    fn restore_from_backup(&mut self) {
        self.data = self.backup.clone().expect("unable revert transaction");
    }

    /// Should be called when call between contracts failed.
    fn restore_from_data(&mut self, data: D) {
        self.data = data;
    }

    /// Should be called when we start a new transaction
    fn create_backup(&mut self) {
        let _ = self.backup.insert(self.data.clone());
    }
}