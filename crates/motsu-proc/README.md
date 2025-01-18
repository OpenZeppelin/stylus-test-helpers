# Motsu's Procedural Macros

This crate contains the `#[motsu::test]` attribute definition used in [`motsu`]. This macro is designed to simplify testing for projects built on Arbitrum Stylus.

[motsu]: ../motsu/README.md

## Usage

### `#[motsu::test]`
The `#[motsu::test]` macro is an enhanced version of Rust's built-in `#[test]` attribute. It is specifically designed for testing within the `Stylus` execution environment.

#### Purpose
This macro enables:
- Access to the **Stylus execution context**, allowing you to interact with contract storage and environment variables like `msg::sender`.
- Enhanced testing capabilities for smart contracts developed on the `Stylus`.
- fallback to standard `#[test]` functionality when no arguments are provided.

#### How It Works
1. If the test function accepts parameters (e.g. `contract`) it provides access to stylus-specific features.
2. If no parameters are passed, it behaves as a standard Rust `#[test]` attribute.

#### Example Usage

```rust
#[cfg(test)]
mod tests {
    use super::*;

    /// Test interacting with contract storage.
    #[motsu::test]
    fn reads_balance(contract: Erc20) {
        // Check initial balance
        let balance = contract.balance_of(Address::ZERO);
        assert_eq!(U256::ZERO, balance);

        // Update balance and verify
        let owner = msg::sender();
        let one = U256::from(1);
        contract._balances.setter(owner).set(one);

        let balance = contract.balance_of(owner);
        assert_eq!(one, balance);
    }

    /// Simple test without parameters.
    #[motsu::test]
    fn simple_test() {
        let value = 42;
        assert_eq!(value, 42);
    }
}
```

---

### Error Handling: `error!` Macro
In addition to `#[motsu::test]`, this crate includes the `error!` macro, which simplifies error handling during macro execution.

#### Purpose
- Provides a way to create descriptive error messages during compile-time.
- Uses the `syn` library to generate errors tied to specific parts of the code.

#### Example Usage

```rust
macro_rules! error {
    ($tokens:expr, $($msg:expr),+ $(,)?) => {{
        let error = syn::Error::new(syn::spanned::Spanned::span(&$tokens), format!($($msg),+));
        return error.to_compile_error().into();
    }};
}
```

#### How It Works
The `error!` macro comes in two forms:
1. **Return a compile-time error:**
   ```rust
   error!(tokens, "An error occurred: {}", some_detail);
   ```
   This generates a compile-time error at the location of `tokens`, with the provided message.

2. **Return an `Err` variant:**
   ```rust
   error!(@ tokens, "Another error occurred.");
   ```
   This form directly returns an `Err` result, allowing for early exits in procedural macro logic.

#### Use Case
The `error!` macro is typically used inside other procedural macros to ensure clear and actionable error messages during macro expansion.

---