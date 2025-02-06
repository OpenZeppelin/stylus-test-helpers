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
//!     fn reads_balance(
//!         contract: Contract<Erc20>,
//!         alice: Account,
//!     ) {  
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
#[cfg(test)]
extern crate alloc;
mod context;
pub mod prelude;
mod router;
mod shims;

pub use motsu_proc::test;

#[cfg(test)]
mod ping_pong_tests {
    #![deny(rustdoc::broken_intra_doc_links)]
    use alloy_primitives::uint;
    use alloy_sol_types::{sol, SolError};
    use stylus_sdk::{
        alloy_primitives::{Address, U256},
        call::Call,
        contract, msg,
        prelude::{public, storage, AddressVM, SolidityError, TopLevelStorage},
        storage::{StorageAddress, StorageU256},
    };

    use crate::context::{Account, Contract};

    #[storage]
    struct PingContract {
        pings_count: StorageU256,
        pinged_from: StorageAddress,
        contract_address: StorageAddress,
    }

    #[public]
    impl PingContract {
        fn ping(&mut self, to: Address, value: U256) -> Result<U256, Vec<u8>> {
            let receiver = IPongContract::new(to);
            let call = Call::new_in(self);
            let value = receiver.pong(call, value)?;

            let pings_count = self.pings_count.get();
            self.pings_count.set(pings_count + ONE);

            self.pinged_from.set(msg::sender());
            self.contract_address.set(contract::address());

            Ok(value)
        }

        fn can_ping(&mut self, to: Address) -> Result<bool, Vec<u8>> {
            let receiver = IPongContract::new(to);
            let call = Call::new_in(self);
            Ok(receiver.can_pong(call)?)
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

            #[allow(missing_docs)]
            function canPong() external view returns (bool);
        }
    }

    sol! {
        #[derive(Debug)]
        #[allow(missing_docs)]
        error MagicError(uint256 value);
    }

    #[derive(SolidityError, Debug)]
    pub enum PongError {
        MagicError(MagicError),
    }

    const MAGIC_ERROR_VALUE: U256 = uint!(42_U256);

    const ONE: U256 = uint!(1_U256);
    const TEN: U256 = uint!(10_U256);

    #[storage]
    struct PongContract {
        pongs_count: StorageU256,
        ponged_from: StorageAddress,
        contract_address: StorageAddress,
    }

    #[public]
    impl PongContract {
        fn pong(&mut self, value: U256) -> Result<U256, PongError> {
            if value == MAGIC_ERROR_VALUE {
                return Err(PongError::MagicError(MagicError { value }));
            }

            let pongs_count = self.pongs_count.get();
            self.pongs_count.set(pongs_count + ONE);

            self.ponged_from.set(msg::sender());
            self.contract_address.set(contract::address());

            Ok(value + ONE)
        }

        fn can_pong(&self) -> bool {
            true
        }
    }

    unsafe impl TopLevelStorage for PongContract {}

    #[motsu_proc::test]
    fn external_call(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Account,
    ) {
        let value = TEN;
        let ponged_value = ping
            .sender(alice)
            .ping(pong.address(), value)
            .expect("should ping successfully");

        assert_eq!(ponged_value, value + ONE);
        assert_eq!(ping.sender(alice).pings_count.get(), ONE);
        assert_eq!(pong.sender(alice).pongs_count.get(), ONE);
    }

    #[motsu_proc::test]
    fn external_call_error(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Account,
    ) {
        let value = MAGIC_ERROR_VALUE;
        let err = ping
            .sender(alice)
            .ping(pong.address(), value)
            .expect_err("should fail to ping");

        assert_eq!(err, MagicError { value }.abi_encode());
    }

    #[motsu_proc::test]
    fn external_static_call(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Account,
    ) {
        let can_ping = ping
            .sender(alice)
            .can_ping(pong.address())
            .expect("should ping successfully");
        assert!(can_ping);
    }

    #[motsu_proc::test]
    fn msg_sender(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Account,
    ) {
        assert_eq!(ping.sender(alice).pinged_from.get(), Address::ZERO);
        assert_eq!(pong.sender(alice).ponged_from.get(), Address::ZERO);

        _ = ping
            .sender(alice)
            .ping(pong.address(), TEN)
            .expect("should ping successfully");

        assert_eq!(ping.sender(alice).pinged_from.get(), alice.address());
        assert_eq!(pong.sender(alice).ponged_from.get(), ping.address());
    }

    #[motsu_proc::test]
    fn has_code(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Account,
    ) {
        assert!(ping.sender(alice).has_pong(pong.address()));
    }

    #[motsu_proc::test]
    fn contract_address(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Account,
    ) {
        assert_eq!(ping.sender(alice).contract_address.get(), Address::ZERO);
        assert_eq!(pong.sender(alice).contract_address.get(), Address::ZERO);

        _ = ping
            .sender(alice)
            .ping(pong.address(), TEN)
            .expect("should ping successfully");

        assert_eq!(ping.sender(alice).contract_address.get(), ping.address());
        assert_eq!(pong.sender(alice).contract_address.get(), pong.address());
    }

    #[motsu_proc::test]
    fn contract_should_not_drop() {
        let alice = Account::random();
        let ping = Contract::<PingContract>::new();
        let mut ping = ping.sender(alice);
        let pong = Contract::<PongContract>::new();
        let pong = pong.sender(alice);

        _ = ping
            .ping(pong.address(), TEN)
            .expect("contract ping should not drop");
    }
}

#[cfg(test)]
mod proxies_tests {
    use alloy_primitives::{address, uint, Address, U256};
    use stylus_sdk::{
        call::Call,
        contract,
        contract::address,
        msg,
        prelude::{public, storage, TopLevelStorage},
        storage::StorageAddress,
    };

    use crate::prelude::*;

    stylus_sdk::stylus_proc::sol_interface! {
        interface IProxy {
            #[allow(missing_docs)]
            function callProxy(uint256 value) external returns (uint256);
            #[allow(missing_docs)]
            function payProxy() external payable;
            #[allow(missing_docs)]
            function passThisMuchToNextProxy(uint256 pass_value) external payable;
            #[allow(missing_docs)]
            function passHalfValueToNextProxy() external payable;
        }
    }

    #[storage]
    struct Proxy {
        next_proxy: StorageAddress,
    }

    #[public]
    impl Proxy {
        fn call_proxy(&mut self, value: U256) -> U256 {
            let next_proxy = self.next_proxy.get();

            // Add one to the value.
            let value = value + ONE;

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

        #[payable]
        fn pay_proxy(&mut self) {
            let next_proxy = self.next_proxy.get();

            // If there is a next proxy.
            if !next_proxy.is_zero() {
                // Add one to the message value.
                let value = msg::value() + ONE;

                // Pay the next proxy.
                let proxy = IProxy::new(next_proxy);
                let call = Call::new_in(self).value(value);
                proxy.pay_proxy(call).expect("should pay proxy");
            }
        }

        #[payable]
        fn pass_proxy_with_fixed_value(&mut self, this_value: U256) {
            let next_proxy = self.next_proxy.get();

            // If there is a next proxy.
            if !next_proxy.is_zero() {
                // Pay the next proxy.
                let proxy = IProxy::new(next_proxy);
                let call = Call::new_in(self).value(this_value);
                let value_for_next_next_proxy = this_value / U256::from(2);
                proxy
                    .pass_this_much_to_next_proxy(
                        call,
                        value_for_next_next_proxy,
                    )
                    .expect("should pass half the value to the next proxy");
            }
        }

        #[payable]
        fn pay_proxy_with_half_balance(&mut self) {
            let next_proxy = self.next_proxy.get();

            // If there is a next proxy.
            if !next_proxy.is_zero() {
                let half_balance = contract::balance() / U256::from(2);
                // Pay the next proxy.
                let proxy = IProxy::new(next_proxy);
                let call = Call::new_in(self).value(half_balance);
                proxy
                    .pass_half_value_to_next_proxy(call)
                    .expect("should pass half the value to the next proxy");
            }
        }
    }

    impl Proxy {
        fn init(&mut self, next_proxy: Address) {
            self.next_proxy.set(next_proxy);
        }
    }

    unsafe impl TopLevelStorage for Proxy {}

    const ONE: U256 = uint!(1_U256);
    const TWO: U256 = uint!(2_U256);
    const FOUR: U256 = uint!(4_U256);
    const EIGHT: U256 = uint!(8_U256);

    const TEN: U256 = uint!(10_U256);

    #[motsu_proc::test]
    fn call_three_proxies(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Account,
    ) {
        // Set up a chain of three proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3.
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(Address::ZERO);

        // Call the first proxy.
        let result = proxy1.sender(alice).call_proxy(TEN);

        // The value is incremented by 1 for each proxy.
        assert_eq!(result, TEN + ONE + ONE + ONE);
    }

    #[motsu_proc::test]
    fn pay_three_proxies(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Account,
    ) {
        // Set up a chain of three proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3.
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(Address::ZERO);

        // Fund accounts.
        alice.fund(TEN);
        proxy1.fund(TEN);
        proxy2.fund(TEN);
        proxy3.fund(TEN);

        // Call the first proxy.
        proxy1.sender_and_value(alice, ONE).pay_proxy();

        // By the end, each actor will lose `ONE`, except last proxy.
        assert_eq!(alice.balance(), TEN - ONE);
        assert_eq!(proxy1.balance(), TEN - ONE);
        assert_eq!(proxy2.balance(), TEN - ONE);
        assert_eq!(proxy3.balance(), TEN + ONE + ONE + ONE);
    }

    #[motsu_proc::test]
    fn pass_proxy_with_fixed_value(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Account,
    ) {
        // Set up a chain of three proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3.
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(Address::ZERO);

        let zero = U256::ZERO;
        let two = uint!(2_U256);
        let four = U256::from(4);
        let eight = U256::from(8);

        // Fund alice, proxies have no funds.
        alice.fund(eight);

        assert_eq!(alice.balance(), eight);
        assert_eq!(proxy1.balance(), zero);
        assert_eq!(proxy2.balance(), zero);
        assert_eq!(proxy3.balance(), zero);

        // Call the first proxy.
        proxy1.sender_and_value(alice, eight).pass_proxy_with_fixed_value(four);

        assert_eq!(alice.balance(), zero);
        assert_eq!(proxy1.balance(), four);
        assert_eq!(proxy2.balance(), two);
        assert_eq!(proxy3.balance(), two);
    }

    #[motsu_proc::test]
    fn pay_proxy_with_half_balance(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Account,
    ) {
        // Set up a chain of three proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3.
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(Address::ZERO);

        let zero = U256::ZERO;
        let two = TWO;
        let four = FOUR;
        let eight = EIGHT;

        // Fund alice, proxies have no funds.
        alice.fund(eight);

        assert_eq!(alice.balance(), eight);
        assert_eq!(proxy1.balance(), zero);
        assert_eq!(proxy2.balance(), zero);
        assert_eq!(proxy3.balance(), zero);

        // Call the first proxy.
        proxy1.sender_and_value(alice, eight).pay_proxy_with_half_balance();

        assert_eq!(alice.balance(), zero);
        assert_eq!(proxy1.balance(), four);
        assert_eq!(proxy2.balance(), two);
        assert_eq!(proxy3.balance(), two);
    }

    #[motsu_proc::test]
    fn no_locks_with_panics() {
        for _ in 0..1000 {
            let proxy1 = Contract::<Proxy>::new();
            let proxy2 = Contract::<Proxy>::new();
            let proxy3 = Contract::<Proxy>::new();
            let alice = Account::random();

            // Set up a chain of three proxies.
            // With the given call chain: proxy1 -> proxy2 -> proxy3.
            proxy1.sender(alice).init(proxy2.address());
            proxy2.sender(alice).init(proxy3.address());
            proxy3.sender(alice).init(Address::ZERO);

            // Call the first proxy.
            let result = proxy1.sender(alice).call_proxy(TEN);

            // The value is incremented by 1 for each proxy.
            assert_eq!(result, TEN + ONE + ONE + ONE);
        }
    }
}
