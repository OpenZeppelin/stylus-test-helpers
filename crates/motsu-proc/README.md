# Motsu's Procedural Macros

This crate contains the `#[motsu::test]` attribute definition used in [`motsu`][motsu]. This macro is designed to simplify testing for smart contracts built with the [Stylus SDK].

[motsu]: ../motsu/README.md
[Stylus SDK]: https://docs.rs/stylus-sdk/latest/stylus_sdk/

## Usage

The `#[motsu::test]` attribute is an enhanced version of Rust's built-in `#[test]` attribute. It is specifically designed for testing within the Stylus execution environment, allowing you to interact with contract storage and environment variables like `msg::sender`.

## Security

Refer to our [Security Policy] for more details.

[Security Policy]: ../../SECURITY.md
