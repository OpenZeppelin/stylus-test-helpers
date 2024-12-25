//! # Motsu - Unit Testing for Stylus
//!
//! This crate enables unit-testing for Stylus contracts. It abstracts away the
//! machinery necessary for writing tests behind a
//! [`#[motsu::test]`][test_attribute] procedural macro.
//!
//! The name `motsu` is an analogy to the place where you put your fingers to
//! hold a stylus pen.
//!
//! ## Usage
//!
//! Annotate tests with [`#[motsu::test]`][test_attribute] instead of `#[test]`
//! to get access to VM affordances.
//!
//! Note that we require contracts to implement
//! `stylus_sdk::prelude::StorageType`. This trait is typically implemented by
//! default with `stylus_proc::sol_storage` or `stylus_proc::storage` macros.
//!
//! ```rust
//! #[cfg(test)]
//! mod tests {
//!     use openzeppelin_stylus::token::erc20::Erc20;
//!     use motsu::prelude::{Account, Contract};
//!     use stylus_sdk::alloy_primitives::{Address, U256};
//!
//!     #[motsu::test]
//!     fn reads_balance(contract: Contract<Erc20>) {
//!         let alice = Account::random();
//!         let balance = contract.sender(alice).balance_of(Address::ZERO); // Access storage.
//!         assert_eq!(balance, U256::ZERO);
//!     }
//! }
//! ```
//!
//! Annotating a test function that accepts no parameters will make
//! [`#[motsu::test]`][test_attribute] behave the same as `#[test]`.
//!
//! ```rust,ignore
//! #[cfg(test)]
//! mod tests {
//!     #[motsu::test] // Equivalent to #[test]
//!     fn test_fn() {
//!         ...
//!     }
//! }
//! ```
//!
//! [test_attribute]: crate::test
mod context;
pub mod prelude;
mod router;
mod shims;

pub use motsu_proc::test;

#[cfg(test)]
mod tests {
    #![deny(rustdoc::broken_intra_doc_links)]
    extern crate alloc;

    use alloy_primitives::uint;
    use stylus_sdk::{
        alloy_primitives::{Address, U256},
        call::Call,
        msg,
        prelude::{public, storage, AddressVM, TopLevelStorage},
        storage::{StorageAddress, StorageU256},
    };

    use crate::context::{Account, Contract};

    #[storage]
    struct PingContract {
        pings_count: StorageU256,
        pinged_from: StorageAddress,
    }

    #[public]
    impl PingContract {
        fn ping(&mut self, to: Address, value: U256) -> Result<U256, Vec<u8>> {
            let receiver = IPongContract::new(to);
            let call = Call::new_in(self);
            let value =
                receiver.pong(call, value).expect("should pong successfully");

            let pings_count = self.pings_count.get();
            self.pings_count.set(pings_count + uint!(1_U256));
            self.pinged_from.set(msg::sender());
            Ok(value)
        }

        fn ping_count(&self) -> U256 {
            self.pings_count.get()
        }

        fn pinged_from(&self) -> Address {
            self.pinged_from.get()
        }

        fn has_pong(&self, to: Address) -> bool {
            to.has_code()
        }
    }

    unsafe impl TopLevelStorage for PingContract {}

    stylus_sdk::stylus_proc::sol_interface! {
        interface IPongContract {
            #[allow(missing_docs)]
            function pong(uint256 value) external returns (uint256);
        }
    }

    #[storage]
    struct PongContract {
        pongs_count: StorageU256,
        ponged_from: StorageAddress,
    }

    #[public]
    impl PongContract {
        pub fn pong(&mut self, value: U256) -> Result<U256, Vec<u8>> {
            let pongs_count = self.pongs_count.get();
            self.pongs_count.set(pongs_count + uint!(1_U256));
            self.ponged_from.set(msg::sender());
            Ok(value + uint!(1_U256))
        }

        fn pong_count(&self) -> U256 {
            self.pongs_count.get()
        }

        fn ponged_from(&self) -> Address {
            self.ponged_from.get()
        }
    }

    unsafe impl TopLevelStorage for PongContract {}

    #[test]
    fn ping_pong_msg_sender() {
        let ping = Contract::<PingContract>::default();
        let pong = Contract::<PongContract>::default();

        let alice = Account::random();

        let value = uint!(10_U256);
        let ponged_value = ping
            .sender(alice)
            .ping(pong.address(), value)
            .expect("should ping successfully");

        assert_eq!(ponged_value, value + uint!(1_U256));
        assert_eq!(ping.sender(alice).ping_count(), uint!(1_U256));
        assert_eq!(pong.sender(alice).pong_count(), uint!(1_U256));

        assert_eq!(ping.sender(alice).pinged_from(), alice.address());
        assert_eq!(pong.sender(alice).ponged_from(), ping.address());
    }

    #[test]
    fn ping_pong_has_code() {
        let ping = Contract::<PingContract>::default();
        let pong = Contract::<PongContract>::default();

        let alice = Account::random();

        assert!(ping.sender(alice).has_pong(pong.address()));
    }

    // TODO#q: add contract::address test

    stylus_sdk::stylus_proc::sol_interface! {
        interface IProxy {
            #[allow(missing_docs)]
            function callProxy(uint256 value) external returns (uint256);
        }
    }

    #[storage]
    pub struct Proxy {
        pub _next_proxy: StorageAddress,
    }

    #[public]
    impl Proxy {
        pub fn call_proxy(&mut self, value: U256) -> U256 {
            let next_proxy = self._next_proxy.get();

            // If there is no next proxy, return the value.
            if next_proxy.is_zero() {
                value
            } else {
                // Otherwise, call the next proxy.
                let proxy = IProxy::new(next_proxy);
                let call = Call::new_in(self);
                proxy.call_proxy(call, value).expect("should call proxy")
            }
        }
    }

    unsafe impl TopLevelStorage for Proxy {}

    #[test]
    fn three_proxies() {
        let proxy1 = Contract::<Proxy>::default();
        let proxy2 = Contract::<Proxy>::default();
        let proxy3 = Contract::<Proxy>::default();

        let alice = Account::random();

        proxy1.init(alice, |storage| {
            storage._next_proxy.set(proxy2.address());
        });
        proxy2.init(alice, |storage| {
            storage._next_proxy.set(proxy3.address());
        });
        proxy3.init(alice, |storage| {
            storage._next_proxy.set(Address::ZERO);
        });

        let value = uint!(10_U256);
        let result = proxy1.sender(alice).call_proxy(value);

        assert_eq!(result, value);
    }
}
