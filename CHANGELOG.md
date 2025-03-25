# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog], and this project adheres to [Semantic Versioning].

[Keep a Changelog]: https://keepachangelog.com/en/1.1.0/
[Semantic Versioning]: https://semver.org/spec/v2.0.0.html

## [Unreleased]

### Added

- Predeploy `EcRecover` precompile contract. #PR_ID
- Derived `PartialEq`, `Eq` and `Debug` for `Account`. #81
- Enabled conversion from `PrivateKeySigner` into `Account`. #81

### Changed (Breaking)

### Changed

## [0.7.0] - 2025-03-19

### Added

- Enabled 'stylus-test' SDK feature by default. #78
- `Account` can be created from string and byte seeds, and can return a signer. #70
- Implemented `Balance` trait for `Account` and `Contract<T>`. #70
- Added ability to set the chain ID in tests. #67

### Changed (Breaking)

- Bump Stylus SDK to `v0.8.3` #77
- `Account` can no longer be created at a predetermined address. #70
- `Funding::balance` is removed. #70

## [0.6.0] - 2025-03-11

### Added

- Fixed bug with invalid size of return data from external call #68
- No randomness in address generation anymore.
  Addresses will be derived from a string representation of the argument name #62
- State of the contract (on-chain data, events) and account balances can be
  reverted when call fails #62
- String representation of address linked to a string tag (argument name),
  that is used for error message formatting #62

### Changed (Breaking)

## [0.5.0] - 2025-03-05

### Added

- Event assertions `Contract::emitted` and `Contract::assert_emitted` #34

### Changed (Breaking)

- Bump Stylus SDK to v0.8.1 #46

## [0.4.0] - 2025-02-11

### Added

- Mocks for the `msg::sender()` #14
- Mocks for the `msg::value()` and `contract::balance()` #31
- Mocks for the external contract calls.
  Two and more contracts can be injected into test #14
- Option to inject `Account` or `Address` in the test #14

### Changed (Breaking)

- `Contract<..>` wrapper is mandatory for the contract's argument #14
- To call contract's function it is mandatory to explicitly indicate the sender,
  through `Contract::<..>::sender(..)` function #14
- `Contract<T>`'s `T` type should implement `TopLevelStorage` #14

## [0.3.0] - 2025-01-07

### Changed (Breaking)

- Bump `motsu` to v0.3.0. #21
- Bump `motsu-proc` to v0.3.0. #20
- Bump `alloy-primitives` and `alloy-sol-types` to v0.8.14. #20
- Bump Stylus SDK to v0.7.0. #17

## [0.2.1] - 2024-12-17

### Added

- Migrate motsu to a new repository.

## [0.2.0] - 2024-11-07

### Added

- Allow tests to be run in parallel.

## [0.1.0] - 2024-10-17

- Initial release
