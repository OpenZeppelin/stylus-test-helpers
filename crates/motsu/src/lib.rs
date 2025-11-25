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
    use alloy_sol_types::{sol, SolEvent};
    use stylus_sdk::{
        alloy_primitives::{Address, U256},
        prelude::{errors::*, *},
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
        #[derive(Debug, PartialEq, Eq)]
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
            self.vm().log(Pinged { from: self.vm().msg_sender(), value });

            let receiver = IPongContract::new(to);
            let call = Call::new_mutating(self);
            let value =
                receiver.pong(self.vm(), call, value).map_err(|err| {
                    let expected = MagicError { value };
                    if expected.clone().encode() == err.encode() {
                        PingError::MagicError(expected)
                    } else {
                        PingError::UnknownError(UnknownError {})
                    }
                })?;

            let pings_count = self.pings_count.get();
            self.pings_count.set(pings_count + ONE);

            self.pinged_from.set(self.vm().msg_sender());
            self.contract_address.set(self.vm().contract_address());

            Ok(value)
        }

        fn can_ping(&mut self, to: Address) -> Result<bool, Vec<u8>> {
            let receiver = IPongContract::new(to);
            let call = Call::new();
            Ok(receiver.can_pong(self.vm(), call)?)
        }

        fn has_pong(&self, to: Address) -> bool {
            self.vm().code_size(to) != 0
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
        #[derive(Debug, PartialEq, Eq)]
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
            self.vm().log(Ponged { from: self.vm().msg_sender(), value });

            if value == MAGIC_ERROR_VALUE {
                return Err(PongError::MagicError(MagicError { value }));
            }

            let pongs_count = self.pongs_count.get();
            self.pongs_count.set(pongs_count + ONE);

            self.ponged_from.set(self.vm().msg_sender());
            self.contract_address.set(self.vm().contract_address());

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

        // Check that events were emitted.
        let all_events = pong1.all_events();
        assert_eq!(all_events.len(), 1, "PongContract should have one event");

        // Drop first contract
        drop(pong1);

        // Second contract at the same address
        let pong2 = Contract::<PongContract>::new_at(addr);

        // Should have fresh state
        assert_eq!(Address::ZERO, pong2.sender(alice).ponged_from.get());
        assert_eq!(U256::ZERO, pong2.sender(alice).pongs_count.get());
        assert_eq!(Address::ZERO, pong2.sender(alice).contract_address.get());

        // Check that the second contract has no events.
        let all_events = pong2.all_events();
        assert!(all_events.is_empty(), "PongContract should have no events");
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

    #[motsu::test]
    fn all_events(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        // Check initial state.
        let ping_events_initial = ping.all_events();
        let pong_events_initial = pong.all_events();
        assert!(
            ping_events_initial.is_empty(),
            "Ping should have no events initially"
        );
        assert!(
            pong_events_initial.is_empty(),
            "Pong should have no events initially"
        );

        // Emit events.
        ping.sender(alice).ping(pong.address(), TEN).motsu_unwrap();
        ping.sender(alice).ping(pong.address(), TEN + ONE).motsu_unwrap();

        // Check both events.
        let ping_events = ping.all_events();
        let pong_events = pong.all_events();

        assert_eq!(ping_events.len(), 2);
        assert_eq!(pong_events.len(), 2);

        // Check event data.
        let ping_event_1 = Pinged::decode_log_data(&ping_events[0]).unwrap();

        assert_eq!(ping_event_1.from, alice);
        assert_eq!(ping_event_1.value, TEN);

        let ping_event_2 = Pinged::decode_log_data(&ping_events[1]).unwrap();

        assert_eq!(ping_event_2.from, alice);
        assert_eq!(ping_event_2.value, TEN + ONE);

        let pong_event_1 = Ponged::decode_log_data(&pong_events[0]).unwrap();

        assert_eq!(pong_event_1.from, ping.address());
        assert_eq!(pong_event_1.value, TEN);

        let pong_event_2 = Ponged::decode_log_data(&pong_events[1]).unwrap();

        assert_eq!(pong_event_2.from, ping.address());
        assert_eq!(pong_event_2.value, TEN + ONE);
    }

    #[motsu::test]
    fn assert_revert_all_event(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        let value_revert = MAGIC_ERROR_VALUE;

        // Check initial state.
        let ping_events_initial = ping.all_events();
        let pong_events_initial = pong.all_events();
        assert!(
            ping_events_initial.is_empty(),
            "Ping should have no events initially"
        );
        assert!(
            pong_events_initial.is_empty(),
            "Pong should have no events initially"
        );

        // Make a call that will revert.
        let _err = ping
            .sender(alice)
            .ping(pong.address(), value_revert)
            .motsu_unwrap_err();

        let ping_events_after_revert = ping.all_events();
        let pong_events_after_revert = pong.all_events();

        assert!(
            ping_events_after_revert.is_empty(),
            "Ping should have no events after revert"
        );
        assert!(
            pong_events_after_revert.is_empty(),
            "Pong should have no events after revert"
        );

        // Make a successful call.
        ping.sender(alice).ping(pong.address(), TEN).motsu_unwrap();

        // Check both events.
        let ping_events = ping.all_events();
        let pong_events = pong.all_events();

        assert_eq!(ping_events.len(), 1);
        assert_eq!(pong_events.len(), 1);

        // Make another call that will revert.
        let _err = ping
            .sender(alice)
            .ping(pong.address(), value_revert)
            .motsu_unwrap_err();

        // Check that events are still the same.
        let ping_events_after_second_revert = ping.all_events();
        let pong_events_after_second_revert = pong.all_events();

        assert_eq!(ping_events_after_second_revert.len(), 1);
        assert_eq!(pong_events_after_second_revert.len(), 1);
    }

    // This test checks that all events are correctly accumulated across
    // multiple instances of the same contract type.
    #[motsu::test]
    fn all_events_multiple_instances_same_type(
        ping1: Contract<PingContract>,
        ping2: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
        bob: Address,
    ) {
        // Initial state: no events.
        assert!(
            ping1.all_events().is_empty(),
            "Ping1 should have no events initially"
        );
        assert!(
            ping2.all_events().is_empty(),
            "Ping2 should have no events initially"
        );

        // Alice pings through `ping1`.
        let value1 = TEN;
        ping1.sender(alice).ping(pong.address(), value1).motsu_unwrap();

        // Check events for `ping1`.
        let ping1_events = ping1.all_events();
        assert_eq!(ping1_events.len(), 1, "Ping1 should have one event");
        let event1_decoded = Pinged::decode_log_data(&ping1_events[0]).unwrap();
        assert_eq!(event1_decoded.from, alice);
        assert_eq!(event1_decoded.value, value1);

        // `ping2` should still have no events.
        assert!(
            ping2.all_events().is_empty(),
            "Ping2 should still have no events after ping1 interaction"
        );

        // Bob pings through `ping2`.
        let value2 = TEN + ONE;
        ping2.sender(bob).ping(pong.address(), value2).motsu_unwrap();

        // Check events for `ping2`.
        let ping2_events = ping2.all_events();
        assert_eq!(ping2_events.len(), 1, "Ping2 should have one event");
        let event2_decoded = Pinged::decode_log_data(&ping2_events[0]).unwrap();
        assert_eq!(event2_decoded.from, bob);
        assert_eq!(event2_decoded.value, value2);

        // Ping1 events should remain unchanged.
        let ping1_events_after_ping2 = ping1.all_events();
        assert_eq!(
            ping1_events_after_ping2.len(),
            1,
            "Ping1 events should not change after ping2 interaction"
        );
        let event1_recheck_decoded =
            Pinged::decode_log_data(&ping1_events_after_ping2[0]).unwrap();
        assert_eq!(event1_recheck_decoded.from, alice);
        assert_eq!(event1_recheck_decoded.value, value1);

        // Check that `pong` contract also has its events.
        let pong_events = pong.all_events();
        assert_eq!(
            pong_events.len(),
            2,
            "Pong contract should have two events from both pings"
        );
    }

    // This test checks that all events are accumulated in order of calls.
    #[motsu::test]
    fn all_events_accumulate_in_order(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
        bob: Address,
    ) {
        // Initial state: no events on `ping` contract.
        assert!(
            ping.all_events().is_empty(),
            "Ping contract should have no events initially"
        );

        // ---- First call to ping by Alice ----
        let value_alice = TEN;
        ping.sender(alice).ping(pong.address(), value_alice).motsu_unwrap();

        let events_after_alice = ping.all_events();
        assert_eq!(
            events_after_alice.len(),
            1,
            "Ping contract should have 1 event after Alice's call"
        );

        // Verify Alice's event.
        let expected_event_alice = Pinged { from: alice, value: value_alice };
        let decoded_event_alice =
            Pinged::decode_log_data(&events_after_alice[0])
                .expect("Failed to decode Alice's Pinged event");
        assert_eq!(
            decoded_event_alice, expected_event_alice,
            "Alice's event data mismatch"
        );

        // ---- Second call to ping by Bob ----
        let value_bob = TEN + ONE;
        ping.sender(bob).ping(pong.address(), value_bob).motsu_unwrap();

        let all_events_now = ping.all_events();
        assert_eq!(
            all_events_now.len(),
            2,
            "Ping contract should have 2 events after Bob's call"
        );

        // Verify Alice's event is still the first one.
        let re_decoded_event_alice =
            Pinged::decode_log_data(&all_events_now[0])
                .expect("Failed to re-decode Alice's Pinged event");
        assert_eq!(
            re_decoded_event_alice, expected_event_alice,
            "Alice's event data mismatch after Bob's call"
        );

        // Verify Bob's event is the second one.
        let expected_event_bob = Pinged { from: bob, value: value_bob };
        let decoded_event_bob = Pinged::decode_log_data(&all_events_now[1])
            .expect("Failed to decode Bob's Pinged event");
        assert_eq!(
            decoded_event_bob, expected_event_bob,
            "Bob's event data mismatch"
        );
    }

    #[motsu::test]
    fn all_events_consistent_on_multiple_calls(
        ping: Contract<PingContract>,
        pong: Contract<PongContract>,
        alice: Address,
    ) {
        // Initial state: no events.
        let initial_events = ping.all_events();
        assert!(initial_events.is_empty());
        // Repeated call to all_events should return the same empty state.
        let initial_events_again = ping.all_events();
        assert_eq!(initial_events, initial_events_again,);

        // Emit one event.
        let value1 = TEN;
        ping.sender(alice).ping(pong.address(), value1).motsu_unwrap();

        // First call to `all_events` after one event.
        let events_after_one_call = ping.all_events();
        assert_eq!(events_after_one_call.len(), 1, "Should be 1 event");

        // Second call to `all_events` immediately after.
        let events_after_one_call_again = ping.all_events();
        assert_eq!(
            events_after_one_call, events_after_one_call_again,
            "Repeated calls after one event should be consistent"
        );

        // Check content of the event.
        let decoded_event1 =
            Pinged::decode_log_data(&events_after_one_call[0]).unwrap();
        let expected_event1 = Pinged { from: alice, value: value1 };
        assert_eq!(decoded_event1, expected_event1);

        // Emit another event.
        let value2 = TEN + ONE;
        ping.sender(alice).ping(pong.address(), value2).motsu_unwrap();

        // First call to `all_events` after two events.
        let events_after_two_calls = ping.all_events();
        assert_eq!(events_after_two_calls.len(), 2, "Should be 2 events");

        // Second call to `all_events` immediately after.
        let events_after_two_calls_again = ping.all_events();
        assert_eq!(
            events_after_two_calls, events_after_two_calls_again,
            "Repeated calls after two events should be consistent"
        );

        // Check content of the two events.
        let decoded_event1_from_two =
            Pinged::decode_log_data(&events_after_two_calls[0]).unwrap();
        assert_eq!(
            decoded_event1_from_two, expected_event1,
            "First event should remain the same"
        );

        let decoded_event2_from_two =
            Pinged::decode_log_data(&events_after_two_calls[1]).unwrap();
        let expected_event2 = Pinged { from: alice, value: value2 };
        assert_eq!(
            decoded_event2_from_two, expected_event2,
            "Second event should be correct"
        );

        // Perform a read-only operation that does not emit events.
        let _pings_count = ping.sender(alice).pings_count.get();

        // Third call to `all_events` after a read operation.
        let events_after_read_op = ping.all_events();
        assert_eq!(
            events_after_two_calls, events_after_read_op,
            "all_events should be consistent after a read-only operation"
        );
    }
}

#[cfg(test)]
mod fallback_receive_tests {
    use stylus_sdk::{
        alloy_primitives::{Address, U256},
        call::call,
        prelude::*,
        storage::{StorageAddress, StorageU256},
    };

    use crate::{
        self as motsu,
        context::{Balance, Contract, Funding},
        revert::ResultExt,
    };

    #[storage]
    struct Implementation {
        value: StorageU256,
    }

    #[public]
    impl Implementation {
        #[payable]
        fn set_value(&mut self, value: U256) {
            self.value.set(value);
        }

        #[receive]
        fn receive(&self) -> Result<(), Vec<u8>> {
            Ok(())
        }
    }

    unsafe impl TopLevelStorage for Implementation {}

    #[storage]
    struct Proxy {
        implementation: StorageAddress,
    }

    unsafe impl TopLevelStorage for Proxy {}

    #[public]
    impl Proxy {
        #[payable]
        fn pass_msg_value(&self) -> Result<Vec<u8>, Vec<u8>> {
            let to = self.implementation.get();
            call(self.vm(), Call::new().value(self.vm().msg_value()), to, &[])
                .map_err(|e| e.into())
        }

        #[payable]
        #[fallback]
        fn fallback(&mut self, calldata: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
            let to = self.implementation.get();
            call(
                self.vm(),
                Call::new().value(self.vm().msg_value()),
                to,
                calldata,
            )
            .map_err(|e| e.into())
        }
    }

    sol_interface! {
        interface IProxy {
            function setValue(uint256 value) external payable;
            function passMsgValue() external payable;
        }
    }

    #[storage]
    struct ProxyCaller;

    unsafe impl TopLevelStorage for ProxyCaller {}

    #[public]
    impl ProxyCaller {
        #[payable]
        fn call_set_value_on_proxy(
            &mut self,
            proxy: Address,
            value: U256,
        ) -> Result<(), Vec<u8>> {
            let i_proxy = IProxy::new(proxy);
            i_proxy
                .set_value(
                    self.vm(),
                    Call::new().value(self.vm().msg_value()),
                    value,
                )
                .map_err(|e| e.into())
        }

        #[payable]
        fn call_non_existent_fn_on_implementation(
            &mut self,
            implementation: Address,
        ) -> Result<(), Vec<u8>> {
            let i_proxy = IProxy::new(implementation);
            i_proxy
                .pass_msg_value(
                    self.vm(),
                    Call::new().value(self.vm().msg_value()),
                )
                .map_err(|e| e.into())
        }
    }

    #[motsu::test]
    fn fallback(
        proxy_caller: Contract<ProxyCaller>,
        proxy: Contract<Proxy>,
        implementation: Contract<Implementation>,
        alice: Address,
    ) {
        proxy.sender(alice).implementation.set(implementation.address());

        let value = U256::from(101);

        proxy_caller
            .sender(alice)
            .call_set_value_on_proxy(proxy.address(), value)
            .motsu_unwrap();

        assert_eq!(implementation.sender(alice).value.get(), value);

        alice.fund(value);

        proxy_caller
            .sender_and_value(alice, value)
            .call_set_value_on_proxy(proxy.address(), U256::ZERO)
            .motsu_unwrap();

        assert_eq!(implementation.sender(alice).value.get(), U256::ZERO);

        assert!(alice.balance().is_zero());
        assert!(proxy.balance().is_zero());
        assert_eq!(implementation.balance(), value);
    }

    #[motsu::test]
    fn fallback_missing(
        proxy_caller: Contract<ProxyCaller>,
        implementation: Contract<Implementation>,
        alice: Address,
    ) {
        let err = proxy_caller
            .sender(alice)
            .call_non_existent_fn_on_implementation(implementation.address())
            .motsu_unwrap_err();

        assert_eq!(
            String::from_utf8(err).unwrap(),
            "function not found for selector '3208857325' and no fallback defined"
        );
    }

    #[motsu::test]
    fn receive(
        proxy: Contract<Proxy>,
        implementation: Contract<Implementation>,
        account: Address,
    ) {
        proxy.sender(account).implementation.set(implementation.address());

        let value = U256::from(101);

        account.fund(value);

        proxy.sender_and_value(account, value).pass_msg_value().unwrap();

        assert!(account.balance().is_zero());
        assert!(proxy.balance().is_zero());
        assert_eq!(implementation.balance(), value);
    }
}

#[cfg(test)]
mod proxies_tests {
    use alloy_primitives::{uint, Address, U256};
    use alloy_sol_types::sol;
    use stylus_sdk::{
        prelude::{errors::MethodError, *},
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

    sol! {
        interface IProxyEncodable {
            #[allow(missing_docs)]
            function delegateCallGetMsgSenderOnProxy(uint8 depth) external returns (address);
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
        #[constructor]
        fn constructor(&mut self, next_proxy: Address) {
            self.next_proxy.set(next_proxy);
        }

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
                let call = Call::new_mutating(self);
                proxy
                    .call_proxy(self.vm(), call, value)
                    .expect("should call proxy")
            }
        }

        #[payable]
        fn pay_proxy(&mut self) {
            let next_proxy = self.next_proxy.get();

            // If there is a next proxy.
            if !next_proxy.is_zero() {
                // Add one to the message value.
                let value = self.vm().msg_value() + ONE;

                // Pay the next proxy.
                let proxy = IProxy::new(next_proxy);
                let call = Call::new_mutating(self).value(value);
                proxy.pay_proxy(self.vm(), call).expect("should pay proxy");
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
                        self.vm(),
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
                let half_balance =
                    self.vm().balance(self.vm().contract_address()) / TWO;
                // Pay the next proxy.
                let proxy = IProxy::new(next_proxy);
                let call = Call::new_mutating(self).value(half_balance);
                proxy
                    .pay_proxy_with_half_balance(self.vm(), call)
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

            let call = Call::new_mutating(self);
            let result = match IProxy::new(next_proxy).try_call_proxy(
                self.vm(),
                call,
                value,
            ) {
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

            let value = self.vm().msg_value() + ONE;

            let call = Call::new_mutating(self).value(value);
            let result =
                match IProxy::new(next_proxy).try_pay_proxy(self.vm(), call) {
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

            if self.vm().msg_value() == FOUR {
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
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(Address::ZERO);

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
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(proxy1.address());

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
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(Address::ZERO);

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
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(Address::ZERO);

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
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(Address::ZERO);

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
            proxy1.sender(alice).constructor(proxy2.address());
            proxy2.sender(alice).constructor(proxy3.address());
            proxy3.sender(alice).constructor(Address::ZERO);

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
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(proxy4.address());
        proxy4.sender(alice).constructor(Address::ZERO);

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
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(proxy4.address());
        proxy4.sender(alice).constructor(Address::ZERO);

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
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(proxy4.address());
        proxy4.sender(alice).constructor(Address::ZERO);

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
mod call_tests {
    use alloy_sol_types::{sol, SolCall, SolValue};
    use stylus_sdk::{
        alloy_primitives::{Address, U256},
        call,
        prelude::*,
        storage::StorageAddress,
    };

    use crate as motsu;
    use crate::prelude::*;

    sol! {
        interface IProxyEncodable {
            #[allow(missing_docs)]
            function delegateCallGetMsgSenderOnProxy(uint8 depth) external returns (address, uint256);
            #[allow(missing_docs)]
            function getMsgSender() external view returns (address);
            #[allow(missing_docs)]
            function getNestedMsgSenderAndOwnMsgSenderUsingRegularCall() external returns (address, address);
        }
    }

    #[storage]
    struct Proxy {
        next_proxy: StorageAddress,
    }

    unsafe impl TopLevelStorage for Proxy {}

    #[public]
    impl Proxy {
        #[constructor]
        fn constructor(&mut self, next_proxy: Address) {
            self.next_proxy.set(next_proxy);
        }

        fn get_msg_sender(&self) -> Address {
            self.vm().msg_sender()
        }

        /// Delegate calls into the next proxy, and returns the msg sender and
        /// value of the next proxy.
        fn delegate_call_get_msg_sender_on_proxy(
            &mut self,
            depth: u8,
        ) -> (Address, U256) {
            if depth == 0 {
                return (self.vm().msg_sender(), self.vm().msg_value());
            }

            let to = self.next_proxy.get();
            let context: IProxyEncodable::delegateCallGetMsgSenderOnProxyCall =
                IProxyEncodable::delegateCallGetMsgSenderOnProxyCall {
                    depth: depth - 1,
                };
            let calldata = context.abi_encode();

            let result = unsafe {
                let call = Call::new_mutating(self);
                call::delegate_call(self.vm(), call, to, &calldata)
                    .expect("should delegate call proxy")
            };

            type Res = (Address, U256);

            Res::abi_decode(&result).expect("should decode address")
        }

        /// Delegate calls into the next proxy and returns the message senders
        /// from the call chain.
        ///
        /// # Returns
        ///
        /// A tuple containing:
        /// * `(Address, Address)`: The message senders from the nested proxy
        ///   call chain
        ///   * First `Address`: The message sender from the next proxy's proxy
        ///   * Second `Address`: The message sender from the next proxy
        /// * `Address`: The current proxy's message sender
        fn get_nested_msg_senders_and_own_msg_sender_using_delegate_call(
            &mut self,
        ) -> ((Address, Address), Address) {
            let calldata = IProxyEncodable::getNestedMsgSenderAndOwnMsgSenderUsingRegularCallCall {}
                .abi_encode();
            let to = self.next_proxy.get();
            let context = Call::new_mutating(self);

            let result = unsafe {
                call::delegate_call(self.vm(), context, to, &calldata)
                    .expect("should delegate call proxy")
            };

            type Res = (Address, Address);

            let nested_msg_senders =
                Res::abi_decode(&result).expect("should decode address");

            (nested_msg_senders, self.vm().msg_sender())
        }

        /// Regular calls into the next proxy and returns the message senders
        /// from the call chain.
        ///
        /// # Returns
        ///
        /// A tuple containing:
        /// - `Address`: The message sender from the next proxy
        /// - `Address`: The current proxy's message sender
        fn get_nested_msg_sender_and_own_msg_sender_using_regular_call(
            &mut self,
        ) -> (Address, Address) {
            let to = self.next_proxy.get();
            let calldata = IProxyEncodable::getMsgSenderCall {}.abi_encode();
            let context = Call::new_mutating(self);

            let result = call::call(self.vm(), context, to, &calldata)
                .expect("should call proxy");

            let nested_msg_sender =
                Address::abi_decode(&result).expect("should decode address");

            (nested_msg_sender, self.vm().msg_sender())
        }
    }

    #[motsu::test]
    fn delegate_call_get_msg_sender_on_proxy_maintains_msg_sender_and_value(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Address,
    ) {
        alice.fund(U256::from(100));
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(Address::ZERO);

        for depth in 0..3 {
            let (nested_msg_sender, nested_msg_value) = proxy1
                .sender(alice)
                .delegate_call_get_msg_sender_on_proxy(depth);
            assert_eq!(nested_msg_sender, alice);
            assert_eq!(nested_msg_value, U256::ZERO);
        }

        // Test with value - only the first call should have the value, while
        // the rest should have zero.

        let value = U256::from(10);
        let (_, msg_value) = proxy1
            .sender_and_value(alice, value)
            .delegate_call_get_msg_sender_on_proxy(0);
        assert_eq!(msg_value, value);

        let (_, nested_msg_value) = proxy1
            .sender_and_value(alice, value)
            .delegate_call_get_msg_sender_on_proxy(1);
        assert_eq!(nested_msg_value, U256::ZERO);
        let (_, nested_msg_value) = proxy1
            .sender_and_value(alice, value)
            .delegate_call_get_msg_sender_on_proxy(2);
        assert_eq!(nested_msg_value, U256::ZERO);
    }

    #[motsu::test]
    fn delegate_call_into_regular_call_updates_msg_sender(
        proxy1: Contract<Proxy>,
        proxy2: Contract<Proxy>,
        proxy3: Contract<Proxy>,
        alice: Address,
    ) {
        proxy1.sender(alice).constructor(proxy2.address());
        proxy2.sender(alice).constructor(proxy3.address());
        proxy3.sender(alice).constructor(Address::ZERO);

        let ((proxy3_msg_sender, proxy2_msg_sender), proxy1_msg_sender) =
            proxy1
                .sender(alice)
                .get_nested_msg_senders_and_own_msg_sender_using_delegate_call(
                );
        assert_eq!(proxy1_msg_sender, alice);
        assert_eq!(proxy2_msg_sender, alice);
        assert_eq!(proxy3_msg_sender, proxy2.address());
    }
}

#[cfg(test)]
mod vm_tests {
    use stylus_sdk::{alloy_primitives::Address, prelude::*};

    use crate as motsu;
    use crate::{
        context::{DEFAULT_BLOCK_TIMESTAMP, DEFAULT_CHAIN_ID},
        prelude::*,
    };

    const ETHEREUM_SEPOLIA_CHAIN_ID: u64 = 11155111;
    const CUSTOM_CHAIN_ID: u64 = 12345678987654321;
    const CUSTOM_BLOCK_TIMESTAMP: u64 = 1_735_689_601;

    #[storage]
    struct ChainDataChecker;

    #[public]
    impl ChainDataChecker {
        fn get_chain_id(&self) -> u64 {
            self.vm().chain_id()
        }

        fn get_block_timestamp(&self) -> u64 {
            self.vm().block_timestamp()
        }
    }

    unsafe impl TopLevelStorage for ChainDataChecker {}

    #[motsu::test]
    fn chain_id(contract: Contract<ChainDataChecker>, alice: Address) {
        // Default chain ID is Arbitrum One
        let chain_id = contract.sender(alice).get_chain_id();
        assert_eq!(chain_id, DEFAULT_CHAIN_ID);

        VM::context().set_chain_id(ETHEREUM_SEPOLIA_CHAIN_ID);

        let chain_id = contract.sender(alice).get_chain_id();
        assert_eq!(chain_id, ETHEREUM_SEPOLIA_CHAIN_ID);

        // Verify that even custom chain ID can be set
        VM::context().set_chain_id(CUSTOM_CHAIN_ID);

        let chain_id = contract.sender(alice).get_chain_id();
        assert_eq!(chain_id, CUSTOM_CHAIN_ID);
    }

    #[motsu::test]
    fn test_block_timestamp(
        contract: Contract<ChainDataChecker>,
        alice: Address,
    ) {
        let timestamp = contract.sender(alice).get_block_timestamp();
        assert_eq!(timestamp, DEFAULT_BLOCK_TIMESTAMP);

        VM::context().set_block_timestamp(CUSTOM_BLOCK_TIMESTAMP);

        let timestamp = contract.sender(alice).get_block_timestamp();
        assert_eq!(timestamp, CUSTOM_BLOCK_TIMESTAMP);
    }
}
