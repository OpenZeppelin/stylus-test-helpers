# Motsu (持つ) - Unit Testing for Stylus

This crate enables unit-testing for Stylus contracts. It abstracts away the
machinery necessary for writing tests behind a `#[motsu::test]` procedural
macro.

`motsu` means ["to hold"](https://jisho.org/word/%E6%8C%81%E3%81%A4) in
Japanese -- we hold a stylus in our hand.

## Usage

This crate enables unit-testing for Stylus contracts. It abstracts away the
machinery necessary for writing tests behind a `#[motsu::test]` procedural macro.

Annotate tests with `#[motsu::test]` instead of `#[test]`
to get access to VM affordances:

 ```rust
 #[cfg(test)]
mod tests {
    use openzeppelin_stylus::token::erc20::Erc20;
    use motsu::prelude::*;

    #[motsu::test]
    fn reads_balance(
        contract: Contract<Erc20>,
        alice: Account,
    ) {
        // Access storage.
        let balance = contract.sender(alice).balance_of(Address::ZERO);
        assert_eq!(balance, U256::ZERO);
    }
}
 ```

Function `Contract::sender()` is necessary to trigger call
to a contract, and should accept an `Account` or `Address` as an argument.

Alternatively `Contract::sender_and_value()` can be used to
pass additional value to the contract:

 ```rust
use motsu::prelude::*;

#[motsu::test]
fn pay_three_proxies(proxy: Contract<Proxy>, alice: Account) {
    let one = uint!(1_U256);
    let ten = uint!(10_U256);

    // Initialize the proxy contract.
    proxy.sender(alice).init(Address::ZERO);

    // Fund alice.
    alice.fund(ten);

    // Call some contract with value.
    proxy.sender_and_value(alice, one).pay_proxy();

    // Assert that alice lost one wei and the proxy gained one wei.
    assert_eq!(alice.balance(), ten - one);
    assert_eq!(proxy.balance(), one);
}
 ```

Multiple external calls are supported in Motsu. Assuming `Proxy` is a
contract that exposes (`#[public]`) function `call_proxy`. Where it adds `one`
to the passed argument and calls next `Proxy` contract at the address
provided during initialization. The following test case can emulate a call
chain of three `Proxy` contracts:

 ```rust
use motsu::prelude::*;

#[motsu::test]
fn call_three_proxies(
    proxy1: Contract<Proxy>,
    proxy2: Contract<Proxy>,
    proxy3: Contract<Proxy>,
    alice: Account,
) {
    let one = uint!(1_U256);
    let ten = uint!(10_U256);

    // Set up a chain of three proxies.
    // With the given call chain: proxy1 -> proxy2 -> proxy3.
    proxy1.sender(alice).init(proxy2.address());
    proxy2.sender(alice).init(proxy3.address());
    proxy3.sender(alice).init(Address::ZERO);

    // Call the first proxy.
    let result = proxy1.sender(alice).call_proxy(ten);

    // The value is incremented by 1 for each proxy.
    assert_eq!(result, ten + one + one + one);
}
 ```

Annotating a test function that accepts no parameters will make
`#[motsu::test]` behave the same as `#[test]`.

 ```rust,ignore
 #[cfg(test)]
mod tests {
    #[motsu::test] // Equivalent to #[test]
    fn test_fn() {
        ...
    }
}
 ```

NOTE!!!
We require a contract to implement unsafe trait
`stylus_sdk::prelude::TopLevelStorage`, for a contract to be used in tests.
Typically, all contracts marked with `#[entrypoint]` will have this trait
automatically derived.
Otherwise, you should do it by
yourself:

 ```rust
 use stylus_sdk::{
    storage::{StorageMap, StorageU256, StorageAddress},
    prelude::*,
    alloy_primitives::Address,
};

// Entry point is not implemented, so we should implement `TopLevelStorage` ourselves.
// #[entrypoint]
#[storage]
pub struct Erc20 {
    balances: StorageMap<Address, StorageU256>,
    allowances: StorageMap<Address, StorageMap<Address, StorageU256>>,
    total_supply: StorageU256,
}

unsafe impl TopLevelStorage for Erc20 {}
 ```

NOTE!!!
For `motsu` to work correctly, `stylus-sdk` should **not** have
default `hostio-caching` feature enabled.

### Notice

We maintain this crate on a best-effort basis. We use it extensively on our own
tests, so we will add here any features and utilities we need for testing our library.

That being said, please do open an issue to start a discussion, keeping in mind
our [code of conduct] and [contribution guidelines].

[code of conduct]: ../../CODE_OF_CONDUCT.md

[contribution guidelines]: ../../CONTRIBUTING.md

## Security

Refer to our [Security Policy](../../SECURITY.md) for more details.
