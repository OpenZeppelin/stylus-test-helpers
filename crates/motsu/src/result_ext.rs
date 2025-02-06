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