# Stylus Test Helpers

Testing in Stylus is limited today. While developing [OpenZeppelin Contracts for Stylus](https://github.com/OpenZeppelin/rust-stylus-contracts) we created a few helpers to test our contracts, and we've decided to open source them and publish them as a separate crate for the community, at least until a more comprehensive testing framework is available.

This crate is a work in progress, and we'll be adding more features and improving the ergonomics as we go. We encourage projects that find this useful to contribute by opening issues and pull requests.

## Motsu (持つ) - Unit Testing for Stylus

This crate enables unit-testing for Stylus contracts. It abstracts away the
machinery necessary for writing tests behind a `#[motsu::test]` procedural
macro.

`motsu` means ["to hold"](https://jisho.org/word/%E6%8C%81%E3%81%A4) in
Japanese -- we hold a stylus in our hand.

### Usage

You can import `motsu` from crates.io by adding the following line to your `Cargo.toml`:

```toml
[dev-dependencies]
motsu = "0.3.0"
```

Then, when writing tests, use `#[motsu::test]` instead of `#[test]` to get access to VM
affordances.

Note that we require contracts to implement `stylus_sdk::prelude::StorageType`.
This trait is typically implemented by default with `stylus_proc::sol_storage`
or `stylus_proc::storage` macros.

```rust
#[cfg(test)]
mod tests {
    use contracts::token::erc20::Erc20;

    #[motsu::test]
    fn reads_balance(contract: Erc20) {
        let balance = contract.balance_of(Address::ZERO); // Access storage.
        assert_eq!(balance, U256::ZERO);
    }
}
```

Annotating a test function that accepts no parameters will make `#[motsu::test]`
behave the same as `#[test]`.

```rust,ignore
#[cfg(test)]
mod tests {
    #[motsu::test]
     fn t() { // If no params, it expands to a `#[test]`.
        // ...
    }
}
```

## Contribute

If you're interested in contributing please check our [contribution guidelines].

[contribution guidelines]: ../../CONTRIBUTING.md

## Security

Refer to our [Security Policy](../../SECURITY.md) for more details.
