# Motsu (持つ) - Unit Testing for Stylus

This crate enables unit-testing for Stylus contracts. It abstracts away the
machinery necessary for writing tests behind a [`#[motsu::test]`][test_attribute] procedural
macro.

`motsu` means ["to hold"][to-hold] in Japanese -- we hold a stylus in our hand.

[to-hold]: https://jisho.org/word/%E6%8C%81%E3%81%A4

## Usage

Annotate tests with [`#[motsu::test]`][test_attribute] instead of `#[test]`
to get access to VM affordances:

```rust
#[cfg(test)]
mod tests {
    use openzeppelin_stylus::token::erc20::{Erc20, IErc20};
    use motsu::prelude::*;

    #[motsu::test]
    fn reads_balance(
        contract: Contract<Erc20>,
        alice: Address,
    ) {
        // Access storage.
        let balance = contract.sender(alice).balance_of(Address::ZERO);
        assert_eq!(balance, U256::ZERO);
    }
}
```

If you need to instantiate an accound that contains a signer and a private key,
you can use [`Account`][account] instead of [`Address`][address]:

```rust
#[cfg(test)]
mod tests {
    use motsu::prelude::*;
    use alloy_signer::SignerSync;

    #[motsu::test]
    fn signs_message(alice: Account) {
        let msg = "message".as_bytes();
        let signer = alice.signer();
        assert!(signer.sign_message_sync(msg).is_ok());
    }
}
```

### Global Variables

Motsu allows you to manipulate certain global variables that affect the
execution environment:

#### Chain ID

You can set the Chain ID in tests using the [`VMContext`][vm_context] API:

```rust,ignore
use motsu::prelude::*;

#[motsu::test]
fn test_with_custom_chain_id(
    contract: Contract<MyContract>,
    alice: Address,
) {
    // Default chain ID is 42161 (Arbitrum One)

    // Set chain ID to 11155111 (Sepolia testnet)
    VMContext::current().set_chain_id(11155111);

    // Now any contract code that depends on `block::chainid()` 
    // will use this value
}
```

### Sender and Value

Function [`Contract::sender()`][contract_sender] is necessary to trigger call to a contract, and
should accept an [`Account`][account] or [`Address`][address] as an
argument.

Alternatively [`Contract::sender_and_value()`][contract_sender_and_value] can be used to pass
additional
value to the contract.
To make a payable call work, user should be funded with [`Funding::fund`][funding_fund] method
(each account has zero balance by default), like in example below:

```rust
use motsu::prelude::*;

#[motsu::test]
fn pay_three_proxies(proxy: Contract<Proxy>, alice: Address) {
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

### External Calls

Multiple external calls are supported in Motsu.
Assuming `Proxy` is a contract that exposes ([`#[public]`][stylus_sdk_public]) function `call_proxy`,
where it adds `one` to the passed argument and calls next `Proxy` contract
at the address provided during initialization.
The following test case can emulate a call chain of three `Proxy` contracts:

```rust
use motsu::prelude::*;

#[motsu::test]
fn call_three_proxies(
    proxy1: Contract<Proxy>,
    proxy2: Contract<Proxy>,
    proxy3: Contract<Proxy>,
    alice: Address,
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

### Checking Events

It is possible to check emitted events by specific contract with
[`Contract::emitted`][contract_emitted] method.
And assert with [`Contract::assert_emitted`][contract_assert_emitted] that will print all matching
events in case of failed assertion.

### Transaction Revert

To revert a transaction in case of `Result::Err`, you should call one of
the following functions:

- [`ResultExt::motsu_unwrap`][result_motsu_unwrap]
- [`ResultExt::motsu_unwrap_err`][result_motsu_unwrap_err]
- [`ResultExt::motsu_expect`][result_motsu_expect]
- [`ResultExt::motsu_expect_err`][result_motsu_expect_err]
- [`ResultExt::motsu_res`][result_motsu_res]

```rust, ignore
const FOUR: U256 = uint!(4_U256);

// If the argument is `FOUR`, the call should revert.
let err = proxy.sender(alice).try_call_proxy(FOUR).motsu_unwrap_err();
assert!(matches!(err, Error::ProxyError(_)));
```

Otherwise, the state of the contract including persistent storage, balances
and emitted events won't be reverted in case of `Result::Err`.

Panics in contract code are not handled as a revert and will fail the test.

### Notes

Annotating a test function that accepts no parameters will make
[`#[motsu::test]`][test_attribute] behave the same as `#[test]`.

```rust,ignore
#[cfg(test)]
mod tests {
    #[motsu::test] // Equivalent to #[test]
    fn test_fn() {
        ...
    }
}
```

**Important:** To use a contract in tests, you must ensure it implements the
unsafe trait [`TopLevelStorage`][stylus_sdk_top_level_storage].
While this trait is automatically derived for contracts marked with
[`#[entrypoint]`][stylus_sdk_entrypoint], you'll need to implement
it manually for any contract without this attribute:

```rust
 use stylus_sdk::{
    storage::{StorageMap, StorageU256, StorageAddress},
    prelude::*,
    alloy_primitives::Address,
};

// Entry point attribute is missing. We should implement `TopLevelStorage` ourselves.
// #[entrypoint]
#[storage]
pub struct Erc20 {
    balances: StorageMap<Address, StorageU256>,
    allowances: StorageMap<Address, StorageMap<Address, StorageU256>>,
    total_supply: StorageU256,
}

unsafe impl TopLevelStorage for Erc20 {}
```

**Important:** For `motsu` to work correctly, `stylus-sdk` should **not** have
a default `hostio-caching` feature enabled.

### Notice

We maintain this crate on a best-effort basis. We use it extensively on our own
tests, so we will add here any features and utilities we need for testing our library.

That being said, please do open an issue to start a discussion, keeping in mind
our [code of conduct] and [contribution guidelines].

[code of conduct]: ../../CODE_OF_CONDUCT.md

[contribution guidelines]: ../../CONTRIBUTING.md

## Security

Refer to our [Security Policy] for more details.

[Security Policy]: ../../SECURITY.md

[test_attribute]: crate::test

[account]: crate::prelude::Account

[address]: stylus_sdk::alloy_primitives::Address

[vm_context]: crate::prelude::VMContext

[contract_sender]: crate::prelude::Contract::sender

[contract_sender_and_value]: crate::prelude::Contract::sender_and_value

[funding_fund]: crate::prelude::Funding::fund

[stylus_sdk_public]: stylus_sdk::prelude::public

[contract_emitted]: crate::prelude::Contract::emitted

[contract_assert_emitted]: crate::prelude::Contract::assert_emitted

[result_motsu_unwrap]: crate::prelude::ResultExt::motsu_unwrap

[result_motsu_unwrap_err]: crate::prelude::ResultExt::motsu_unwrap_err

[result_motsu_expect]: crate::prelude::ResultExt::motsu_expect

[result_motsu_expect_err]: crate::prelude::ResultExt::motsu_expect_err

[result_motsu_res]: crate::prelude::ResultExt::motsu_res

[stylus_sdk_top_level_storage]: stylus_sdk::prelude::TopLevelStorage

[stylus_sdk_entrypoint]: stylus_sdk::prelude::entrypoint