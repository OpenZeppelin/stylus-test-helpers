#![doc = include_str!("../README.md")]
#![allow(deprecated)]
extern crate alloc;

mod context;
mod precompiles;
pub mod prelude;
mod revert;
mod router;
mod shims;
mod storage_access;

pub use motsu_proc::test;

#[cfg(test)]
mod ping_pong_tests {
    #![deny(rustdoc::broken_intra_doc_links)]
    use alloy_primitives::uint;
    use alloy_sol_types::sol;
    use stylus_sdk::{
        alloy_primitives::{Address, U256},
        call::{Call, MethodError},
        contract, evm, msg,
        prelude::*,
        storage::{StorageAddress, StorageU256},
    };

    use crate as motsu;
    use crate::prelude::*;

    const ONE: U256 = uint!(1_U256);
    const TEN: U256 = uint!(10_U256);
    const MAGIC_ERROR_VALUE: U256 = uint!(42_U256);

    sol! {
        /// Emitted when [`PingContract`] is called.
        ///
        /// * `from` - Address from which the contract was pinged.
        /// * `value` - Value received when pinged.
        #[allow(missing_docs)]
        #[derive(Debug)]
        event Pinged(
            address indexed from,
            uint256 indexed value
        );
    }

    sol! {
        #[derive(Debug)]
        #[allow(missing_docs)]
        error MagicError(uint256 value);
        #[derive(Debug)]
        #[allow(missing_docs)]
        error UnknownError();
    }

    #[derive(SolidityError, Debug)]
    pub enum PingError {
        MagicError(MagicError),
        UnknownError(UnknownError),
    }

    #[storage]
    struct PingContract {
        pings_count: StorageU256,
        pinged_from: StorageAddress,
        contract_address: StorageAddress,
    }

    #[public]
    impl PingContract {
        fn ping(
            &mut self,
            to: Address,
            value: U256,
        ) -> Result<U256, PingError> {
            evm::log(Pinged { from: msg::sender(), value });

            let receiver = IPongContract::new(to);
            let call = Call::new_in(self);
            let value = receiver.pong(call, value).map_err(|err| {
                let expected = MagicError { value };
                if expected.clone().encode() == err.encode() {
                    PingError::MagicError(expected)
                } else {
                    PingError::UnknownError(UnknownError {})
                }
            })?;

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

    #[derive(SolidityError, Debug)]
    pub enum PongError {
        MagicError(MagicError),
    }

    sol! {
        /// Emitted when [`PongContract`] is called.
        ///
        /// * `from` - Address from which the contract was ponged.
        /// * `value` - Value received when ponged.
        #[allow(missing_docs)]
        #[derive(Debug)]
        event Ponged(
            address indexed from,
            uint256 indexed value
        );
    }

    #[storage]
    struct PongContract {
        pongs_count: StorageU256,
        ponged_from: StorageAddress,
        contract_address: StorageAddress,
    }

    #[public]
    impl PongContract {
        fn pong(&mut self, value: U256) -> Result<U256, PongError> {
            evm::log(Ponged { from: msg::sender(), value });

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

    #[motsu::test]
    fn external_call(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        let value = TEN;
        let ponged_value =
            ping.sender(alice).ping(pong.address(), value).motsu_unwrap();

        assert_eq!(ponged_value, value + ONE);
        assert_eq!(ping.sender(alice).pings_count.get(), ONE);
        assert_eq!(pong.sender(alice).pongs_count.get(), ONE);
    }

    #[motsu::test]
    fn external_call_error(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        let value = MAGIC_ERROR_VALUE;
        let err =
            ping.sender(alice).ping(pong.address(), value).motsu_unwrap_err();

        assert!(
            matches!(err, PingError::MagicError(MagicError { value }) if value == value)
        );
    }

    #[motsu::test]
    #[should_panic = "account alice failed to call ping: MagicError(MagicError { value: 42 })"]
    fn external_call_panic(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        let value = MAGIC_ERROR_VALUE;
        ping.sender(alice).ping(pong.address(), value).motsu_unwrap();
    }

    #[motsu::test]
    fn external_static_call(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        let can_ping =
            ping.sender(alice).can_ping(pong.address()).motsu_unwrap();
        assert!(can_ping);
    }

    #[motsu::test]
    fn msg_sender(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        assert_eq!(ping.sender(alice).pinged_from.get(), Address::ZERO);
        assert_eq!(pong.sender(alice).ponged_from.get(), Address::ZERO);

        ping.sender(alice).ping(pong.address(), TEN).motsu_unwrap();

        assert_eq!(ping.sender(alice).pinged_from.get(), alice);
        assert_eq!(pong.sender(alice).ponged_from.get(), ping.address());
    }

    #[motsu::test]
    fn has_code(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        assert!(ping.sender(alice).has_pong(pong.address()));
    }

    #[motsu::test]
    fn contract_address(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        assert_eq!(ping.sender(alice).contract_address.get(), Address::ZERO);
        assert_eq!(pong.sender(alice).contract_address.get(), Address::ZERO);

        ping.sender(alice).ping(pong.address(), TEN).motsu_unwrap();

        assert_eq!(ping.sender(alice).contract_address.get(), ping.address());
        assert_eq!(pong.sender(alice).contract_address.get(), pong.address());
    }

    #[motsu::test]
    fn deref_invalidated_storage_cache(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        // This test is different from `contract_address` test, since it checks
        // that `StorageType` contract correctly resets.
        let mut alice_ping = ping.sender(alice);
        let alice_pong = pong.sender(alice);

        // `alice_pong.contract_address.get()` invocation will cache the value
        // of `contract_address` for the next immutable call.
        assert_eq!(alice_pong.contract_address.get(), Address::ZERO);

        // Here `alice` calls `ping` contract and should implicitly change
        // `pong.contract_address`.
        alice_ping.ping(pong.address(), TEN).motsu_unwrap();

        // And we will check that we're not reading cached `Address::ZERO`
        // value, but the actual one.
        assert_eq!(alice_pong.contract_address.get(), pong.address());
    }

    #[motsu::test]
    #[should_panic(expected = "contract storage already initialized")]
    fn storage_duplicate_contract() {
        let addr = Address::random();

        // Create the first contract instance.
        let _ping1 = Contract::<PingContract>::new_at(addr);

        // Attempt to create the second instance at the same address should
        // fail.
        let _ping2 = Contract::<PingContract>::new_at(addr);
    }

    // Although the same address is very unlikely to be reused on the actual
    // chain, this is still an allowed "feature" of motsu, so we "document" the
    // behavior with this unit test.
    #[motsu::test]
    fn storage_cleanup(alice: Address, addr: Address) {
        // First contract
        let pong1 = Contract::<PongContract>::new_at(addr);

        pong1.sender(alice).pong(U256::ZERO).expect("should pong");

        assert_eq!(alice, pong1.sender(alice).ponged_from.get());
        assert_eq!(ONE, pong1.sender(alice).pongs_count.get());
        assert_eq!(addr, pong1.sender(alice).contract_address.get());

        // Drop first contract
        drop(pong1);

        // Second contract at the same address
        let pong2 = Contract::<PongContract>::new_at(addr);

        // Should have fresh state
        assert_eq!(Address::ZERO, pong2.sender(alice).ponged_from.get());
        assert_eq!(U256::ZERO, pong2.sender(alice).pongs_count.get());
        assert_eq!(Address::ZERO, pong2.sender(alice).contract_address.get());
    }

    #[motsu::test]
    fn emits_event(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        ping.sender(alice).ping(pong.address(), TEN).motsu_unwrap();

        // Assert emitted events.
        ping.assert_emitted(&Pinged { from: alice, value: TEN });
        pong.assert_emitted(&Ponged { from: ping.address(), value: TEN });

        // Assert not emitted events
        assert!(!ping.emitted(&Pinged { from: ping.address(), value: TEN }));
        assert!(!pong.emitted(&Ponged { from: alice, value: TEN }));
        assert!(!ping.emitted(&Pinged { from: alice, value: TEN + ONE }));
        assert!(
            !pong.emitted(&Ponged { from: ping.address(), value: TEN + ONE })
        );
    }

    #[motsu::test]
    #[should_panic(
        expected = "event was not emitted, matching events: [Pinged { from: alice, value: 10 }]"
    )]
    fn asserted_emitted_event(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        ping.sender(alice).ping(pong.address(), TEN).motsu_unwrap();

        // Check panic assertion.
        let wrong_from = ping.address();
        ping.assert_emitted(&Pinged { from: wrong_from, value: TEN });
    }

    #[motsu::test]
    #[should_panic(
        expected = "event was not emitted, no matching events found"
    )]
    fn assert_reverts_emitted_event(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        let value = MAGIC_ERROR_VALUE;
        ping.sender(alice).ping(pong.address(), value).motsu_unwrap_err();

        // Both events should not be emitted after revert.
        assert!(!ping.emitted(&Pinged { from: alice, value }));
        assert!(!pong.emitted(&Ponged { from: ping.address(), value }));

        // Check panic assertion.
        ping.assert_emitted(&Pinged { from: alice, value });
    }
}

#[cfg(test)]
mod proxies_tests {
    use alloy_primitives::{uint, Address, U256};
    use alloy_sol_types::sol;
    use stylus_sdk::{
        call::{Call, MethodError},
        contract, msg,
        prelude::*,
        storage::{StorageAddress, StorageU256},
    };

    use crate as motsu;
    use crate::prelude::*;

    const ONE: U256 = uint!(1_U256);
    const TWO: U256 = uint!(2_U256);
    const THREE: U256 = uint!(3_U256);
    const FOUR: U256 = uint!(4_U256);
    const EIGHT: U256 = uint!(8_U256);
    const TEN: U256 = uint!(10_U256);
    const CALL_PROXY_LIMIT: U256 = uint!(50_U256);

    stylus_sdk::stylus_proc::sol_interface! {
        interface IProxy {
            #[allow(missing_docs)]
            function callProxy(uint256 value) external returns (uint256);
            #[allow(missing_docs)]
            function tryCallProxy(uint256 value) external returns (uint256);
            #[allow(missing_docs)]
            function payProxy() external payable;
            #[allow(missing_docs)]
            function tryPayProxy() external payable;
            #[allow(missing_docs)]
            function passProxyWithFixedValue(uint256 pass_value) external payable;
            #[allow(missing_docs)]
            function payProxyWithHalfBalance() external payable;
        }
    }

    #[storage]
    struct Proxy {
        next_proxy: StorageAddress,
        received_value: StorageU256,
    }

    sol! {
        #[derive(Debug)]
        #[allow(missing_docs)]
        error ProxyError();

        #[derive(Debug)]
        #[allow(missing_docs)]
        error UnknownError();
    }

    #[derive(SolidityError, Debug)]
    pub enum Error {
        ProxyError(ProxyError),
        UnknownError(UnknownError),
    }

    #[public]
    impl Proxy {
        fn call_proxy(&mut self, value: U256) -> U256 {
            if value == CALL_PROXY_LIMIT {
                return value;
            }

            // Add one to the value.
            let value = value + ONE;

            // If there is no next proxy, return the value.
            let next_proxy = self.next_proxy.get();
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
        fn pass_proxy_with_fixed_value(&self, this_value: U256) {
            let next_proxy = self.next_proxy.get();

            // If there is a next proxy.
            if !next_proxy.is_zero() {
                // Pay the next proxy.
                let proxy = IProxy::new(next_proxy);
                let call = Call::new().value(this_value);
                let value_for_next_next_proxy = this_value / TWO;
                proxy
                    .pass_proxy_with_fixed_value(
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
                let half_balance = contract::balance() / TWO;
                // Pay the next proxy.
                let proxy = IProxy::new(next_proxy);
                let call = Call::new_in(self).value(half_balance);
                proxy
                    .pay_proxy_with_half_balance(call)
                    .expect("should pass half the value to the next proxy");
            }
        }

        /// Accept `value` as an argument and call the next proxy with `ONE +
        /// value`.
        /// Tries to recover transaction if [`Error::ProxyError`] received.
        ///
        /// # Errors
        ///
        /// * If `value` is `FOUR` or there is no next proxy, returns
        ///   [`Error::ProxyError`].
        /// * If unknown error received from the next proxy, returns
        ///   [`Error::UnknownError`].
        fn try_call_proxy(&mut self, value: U256) -> Result<U256, Error> {
            // Set the received value to check how revert works.
            self.received_value.set(value);

            let next_proxy = self.next_proxy.get();
            if next_proxy.is_zero() {
                return Err(Error::ProxyError(ProxyError {}));
            }

            let value = value + ONE;

            let result = match IProxy::new(next_proxy)
                .try_call_proxy(Call::new_in(self), value)
            {
                Ok(value) => Ok(value),
                Err(err) => {
                    // Handle `ProxyError` and return `Ok` with the value.
                    let expected_err = ProxyError {};
                    if err.encode() == expected_err.clone().encode() {
                        Ok(value)
                    } else {
                        Err(Error::UnknownError(UnknownError {}))
                    }
                }
            };

            if self.received_value.get() == FOUR {
                return Err(Error::ProxyError(ProxyError {}));
            }

            result
        }

        /// Accept payment and pay to the next proxy with `ONE + msg
        /// value`.
        /// Tries to recover transaction if [`Error::ProxyError`] received.
        ///
        /// # Errors
        ///
        /// * If msg value is `FOUR` or there is no next proxy, returns
        ///   [`Error::ProxyError`].
        /// * If unknown error received from the next proxy, returns
        ///   [`Error::UnknownError`].
        #[payable]
        fn try_pay_proxy(&mut self) -> Result<(), Error> {
            let next_proxy = self.next_proxy.get();
            if next_proxy.is_zero() {
                return Err(Error::ProxyError(ProxyError {}));
            }

            let value = msg::value() + ONE;

            let result = match IProxy::new(next_proxy)
                .try_pay_proxy(Call::new_in(self).value(value))
            {
                Ok(_) => Ok(()),
                Err(err) => {
                    // Handle `ProxyError` and return `Ok`.
                    let expected_err = ProxyError {};
                    if err.encode() == expected_err.clone().encode() {
                        Ok(())
                    } else {
                        Err(Error::UnknownError(UnknownError {}))
                    }
                }
            };

            if msg::value() == FOUR {
                return Err(Error::ProxyError(ProxyError {}));
            }

            result
        }

        fn received_value(&self) -> U256 {
            self.received_value.get()
        }

        #[allow(clippy::unnecessary_wraps)]
        fn replace_received_value(
            &mut self,
            value: U256,
        ) -> Result<U256, Vec<u8>> {
            let previous = self.received_value();
            self.received_value.set(value);
            Ok(previous)
        }
    }

    impl Proxy {
        fn init(&mut self, next_proxy: Address) {
            self.next_proxy.set(next_proxy);
        }
    }

    unsafe impl TopLevelStorage for Proxy {}

    #[motsu::test]
    fn call_three_proxies(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Address,
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

    #[motsu::test]
    fn call_three_proxies_with_reentrancy(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Address,
    ) {
        // Set up a chain of three proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3 -> proxy1 -> ..
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(proxy1.address());

        // Call the first proxy.
        let result = proxy1.sender(alice).call_proxy(ONE);

        // Reentrant call should stop with limit.
        assert_eq!(result, CALL_PROXY_LIMIT);
    }

    #[motsu::test]
    fn pay_three_proxies(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Address,
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

    #[motsu::test]
    fn pass_proxy_with_fixed_value(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Address,
    ) {
        // Set up a chain of three proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3.
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(Address::ZERO);

        // Fund alice, proxies have no funds.
        alice.fund(EIGHT);

        assert_eq!(alice.balance(), EIGHT);
        assert_eq!(proxy1.balance(), U256::ZERO);
        assert_eq!(proxy2.balance(), U256::ZERO);
        assert_eq!(proxy3.balance(), U256::ZERO);

        // Call the first proxy.
        proxy1.sender_and_value(alice, EIGHT).pass_proxy_with_fixed_value(FOUR);

        assert_eq!(alice.balance(), U256::ZERO);
        assert_eq!(proxy1.balance(), FOUR);
        assert_eq!(proxy2.balance(), TWO);
        assert_eq!(proxy3.balance(), TWO);
    }

    #[motsu::test]
    fn pay_proxy_with_half_balance(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Address,
    ) {
        // Set up a chain of three proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3.
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(Address::ZERO);

        // Fund alice, proxies have no funds.
        alice.fund(EIGHT);

        assert_eq!(alice.balance(), EIGHT);
        assert_eq!(proxy1.balance(), U256::ZERO);
        assert_eq!(proxy2.balance(), U256::ZERO);
        assert_eq!(proxy3.balance(), U256::ZERO);

        // Call the first proxy.
        proxy1.sender_and_value(alice, EIGHT).pay_proxy_with_half_balance();

        assert_eq!(alice.balance(), U256::ZERO);
        assert_eq!(proxy1.balance(), FOUR);
        assert_eq!(proxy2.balance(), TWO);
        assert_eq!(proxy3.balance(), TWO);
    }

    #[motsu::test]
    fn no_locks_with_panics() {
        // Checks that Motsu VM locking behavior is correct when running the
        // same test multiple times on the same thread.
        for _ in 0..1000 {
            let proxy1 = Contract::<Proxy>::new();
            let proxy2 = Contract::<Proxy>::new();
            let proxy3 = Contract::<Proxy>::new();
            let alice = Address::random();

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

    #[motsu::test]
    fn try_call_and_revert_to_previous_state(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        proxy4: Contract<Proxy>,
        alice: Address,
    ) {
        // Set up a chain of four proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3 -> proxy4.
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(proxy4.address());
        proxy4.sender(alice).init(Address::ZERO);

        // Try to replace received value and process result with `motsu_res()`
        _ = proxy1.sender(alice).replace_received_value(ONE).motsu_res();
        _ = proxy2.sender(alice).replace_received_value(TWO).motsu_res();
        _ = proxy3.sender(alice).replace_received_value(THREE).motsu_res();
        _ = proxy4.sender(alice).replace_received_value(FOUR).motsu_res();

        // If the argument is `FOUR`, the call should revert fully.
        let err = proxy1.sender(alice).try_call_proxy(FOUR).motsu_unwrap_err();
        assert!(matches!(err, Error::ProxyError(_)));
        // And the state should be as before failed transaction.
        assert_eq!(proxy1.sender(alice).received_value(), ONE);
        assert_eq!(proxy2.sender(alice).received_value(), TWO);
        assert_eq!(proxy3.sender(alice).received_value(), THREE);
        assert_eq!(proxy4.sender(alice).received_value(), FOUR);

        // Try to replace received value and do not process the result.
        _ = proxy1.sender(alice).replace_received_value(TEN);
        _ = proxy2.sender(alice).replace_received_value(TEN);
        _ = proxy3.sender(alice).replace_received_value(TEN);
        _ = proxy4.sender(alice).replace_received_value(TEN);

        // If the argument is `FOUR`, the call should revert fully.
        let err = proxy1.sender(alice).try_call_proxy(FOUR).motsu_unwrap_err();
        assert!(matches!(err, Error::ProxyError(_)));
        // And the state should be as before failed transaction.
        assert_eq!(proxy1.sender(alice).received_value(), TEN);
        assert_eq!(proxy2.sender(alice).received_value(), TEN);
        assert_eq!(proxy3.sender(alice).received_value(), TEN);
        assert_eq!(proxy4.sender(alice).received_value(), TEN);
    }

    #[motsu::test]
    fn try_call_and_revert_partially(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        proxy4: Contract<Proxy>,
        alice: Address,
    ) {
        // Set up a chain of four proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3 -> proxy4.
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(proxy4.address());
        proxy4.sender(alice).init(Address::ZERO);

        // If the argument is `FOUR`, the call should revert fully.
        let err = proxy1.sender(alice).try_call_proxy(FOUR).motsu_unwrap_err();
        assert!(matches!(err, Error::ProxyError(_)));
        assert_eq!(proxy1.sender(alice).received_value(), U256::ZERO);
        assert_eq!(proxy2.sender(alice).received_value(), U256::ZERO);
        assert_eq!(proxy3.sender(alice).received_value(), U256::ZERO);
        assert_eq!(proxy4.sender(alice).received_value(), U256::ZERO);

        // If the argument is `THREE`,
        let result = proxy1.sender(alice).try_call_proxy(THREE).motsu_unwrap();
        assert_eq!(result, FOUR);
        assert_eq!(proxy1.sender(alice).received_value(), THREE);
        // call to the second proxy should revert.
        assert_eq!(proxy2.sender(alice).received_value(), U256::ZERO);
        assert_eq!(proxy3.sender(alice).received_value(), U256::ZERO);
        assert_eq!(proxy4.sender(alice).received_value(), U256::ZERO);

        // If the argument is `TWO`,
        let result = proxy1.sender(alice).try_call_proxy(TWO).motsu_unwrap();
        assert_eq!(result, FOUR);
        assert_eq!(proxy1.sender(alice).received_value(), TWO);
        assert_eq!(proxy2.sender(alice).received_value(), THREE);
        // call to the third proxy should revert.
        assert_eq!(proxy3.sender(alice).received_value(), U256::ZERO);
        assert_eq!(proxy4.sender(alice).received_value(), U256::ZERO);

        // If the argument is `ONE`,
        let result = proxy1.sender(alice).try_call_proxy(ONE).motsu_unwrap();
        assert_eq!(result, FOUR);
        assert_eq!(proxy1.sender(alice).received_value(), ONE);
        assert_eq!(proxy2.sender(alice).received_value(), TWO);
        assert_eq!(proxy3.sender(alice).received_value(), THREE);
        // call to the fourth proxy should revert.
        assert_eq!(proxy4.sender(alice).received_value(), U256::ZERO);
    }

    #[motsu::test]
    fn try_pay_and_revert_partially(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        proxy4: Contract<Proxy>,
        alice: Address,
    ) {
        // Set up a chain of four proxies.
        // With the given call chain: proxy1 -> proxy2 -> proxy3 -> proxy4.
        proxy1.sender(alice).init(proxy2.address());
        proxy2.sender(alice).init(proxy3.address());
        proxy3.sender(alice).init(proxy4.address());
        proxy4.sender(alice).init(Address::ZERO);

        // Fund all accounts.
        alice.fund(TEN);
        proxy1.fund(TEN);
        proxy2.fund(TEN);
        proxy3.fund(TEN);
        proxy4.fund(TEN);

        // If the msg value is `FOUR`, the call should revert fully.
        let err = proxy1
            .sender_and_value(alice, FOUR)
            .try_pay_proxy()
            .motsu_unwrap_err();
        assert!(matches!(err, Error::ProxyError(_)));
        // Balances should remain the same.
        assert_eq!(alice.balance(), TEN);
        assert_eq!(proxy1.balance(), TEN);
        assert_eq!(proxy2.balance(), TEN);
        assert_eq!(proxy3.balance(), TEN);
        assert_eq!(proxy4.balance(), TEN);

        // If the msg value is `ONE`,
        proxy1.sender_and_value(alice, ONE).try_pay_proxy().motsu_unwrap();
        assert_eq!(alice.balance(), TEN - ONE);
        assert_eq!(proxy1.balance(), TEN - ONE);
        assert_eq!(proxy2.balance(), TEN - ONE);
        // the third proxy should receive funds,
        assert_eq!(proxy3.balance(), TEN + THREE);
        // and call to the fourth proxy should revert.
        assert_eq!(proxy4.balance(), TEN);
    }
}

#[cfg(test)]
mod vm_tests {
    use stylus_sdk::{alloy_primitives::Address, block, prelude::*};

    use crate as motsu;
    use crate::{context::DEFAULT_CHAIN_ID, prelude::*};

    const ETHEREUM_SEPOLIA_CHAIN_ID: u64 = 11155111;
    const CUSTOM_CHAIN_ID: u64 = 12345678987654321;

    #[storage]
    struct ChainChecker;

    #[public]
    impl ChainChecker {
        fn get_chain_id(&self) -> u64 {
            block::chainid()
        }
    }

    unsafe impl TopLevelStorage for ChainChecker {}

    #[motsu::test]
    fn reads_balance(contract: Contract<Erc20>, alice: Address) {
        // `contract` is already set up
        let balance = contract.sender(alice).balance_of(Address::ZERO);
        assert_eq!(U256::ZERO, balance);

        let owner = msg::sender();
        let one = U256::from(1);
        contract.sender(alice)._balances.setter(owner).set(one);
        let balance = contract.sender(alice).balance_of(owner);
        assert_eq!(one, balance);
    }

    #[motsu::test]
    fn chain_id(contract: Contract<ChainChecker>, alice: Address) {
        // Default chain ID is Arbitrum One
        let chain_id = contract.sender(alice).get_chain_id();
        assert_eq!(chain_id, DEFAULT_CHAIN_ID);
        // Verify the correct chain ID is returned within tests too
        assert_eq!(block::chainid(), DEFAULT_CHAIN_ID);

        VMContext::current().set_chain_id(ETHEREUM_SEPOLIA_CHAIN_ID);

        let chain_id = contract.sender(alice).get_chain_id();
        assert_eq!(chain_id, ETHEREUM_SEPOLIA_CHAIN_ID);
        assert_eq!(block::chainid(), ETHEREUM_SEPOLIA_CHAIN_ID);

        // Verify that even custom chain ID can be set
        VMContext::current().set_chain_id(CUSTOM_CHAIN_ID);

        let chain_id = contract.sender(alice).get_chain_id();
        assert_eq!(chain_id, CUSTOM_CHAIN_ID);
        assert_eq!(block::chainid(), CUSTOM_CHAIN_ID);
    }
}
