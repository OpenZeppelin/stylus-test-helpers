# Stylus Test Helpers

Testing in Stylus is limited today. While
developing [OpenZeppelin Contracts for Stylus](https://github.com/OpenZeppelin/rust-contracts-stylus) we created a few
helpers to test our contracts, and we've decided to open source them and publish them as a separate crate for the
community, at least until a more comprehensive testing framework is available.

This crate is a work in progress, and we'll be adding more features and improving the ergonomics as we go. We encourage
projects that find this useful to contribute by opening issues and pull requests.

## Motsu (持つ) - Unit Testing for Stylus

This crate enables unit-testing for Stylus contracts. It abstracts away the
machinery necessary for writing tests behind a `#[motsu::test]` procedural
macro.

`motsu` means ["to hold"](https://jisho.org/word/%E6%8C%81%E3%81%A4) in
Japanese -- we hold a stylus in our hand.

### Usage

You can import `motsu` from crates.io by adding the following line to your `Cargo.toml`.
For `motsu` to work correctly, `stylus-sdk` should **not** have a default `hostio-caching`
feature enabled, like:

```toml
[dev-dependencies]
motsu = "0.4.0"
stylus-sdk = { version = "0.7.0", default-features = false, features = [
  "mini-alloc",
] }
```

## Contribute

If you're interested in contributing please check our [contribution guidelines].

[contribution guidelines]: ./CONTRIBUTING.md

## Security

Refer to our [Security Policy](./SECURITY.md) for more details.
