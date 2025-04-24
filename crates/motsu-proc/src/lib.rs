#![doc = include_str!("../README.md")]
use proc_macro::TokenStream;

/// Shorthand to print nice errors.
///
/// Note that it's defined before the module declarations.
macro_rules! error {
    ($tokens:expr, $($msg:expr),+ $(,)?) => {{
        let error = syn::Error::new(syn::spanned::Spanned::span(&$tokens), format!($($msg),+));
        return error.to_compile_error().into();
    }};
    (@ $tokens:expr, $($msg:expr),+ $(,)?) => {{
        return Err(syn::Error::new(syn::spanned::Spanned::span(&$tokens), format!($($msg),+)))
    }};
}

mod test;

/// Defines a unit test that provides access to Stylus' execution context.
///
/// Internally, this is a thin wrapper over `#[test]` that gives access to
/// affordances like contract storage and `msg::sender` and deploys precompiles.
/// If you don't need them, you can simply use `#[test]` instead of
/// `#[motsu::test]`.
///
/// # Examples
///
/// ```rust,ignore
/// #[cfg(test)]
/// mod tests {
///     #[motsu::test]
///     fn autosetup(contract: Contract<Erc20>, alice: Address) {
///         // contract and alice is already set up, and precompiled
///         // contracts are deployed.
///
///         // ...
///     }
///
///     #[motsu::test]
///     fn no_affordances() {
///         // only precompiled contracts are deployed, contract and alice
///         // need to be manually instantiated.
///         let contract = Contract::<Erc20>::from_tag("contract");
///         let alice = Address::from_tag("alice");
///
///         // ...
///     }
///
///     #[test]
///     fn manual_setup() {
///         // CAUTION: precompiles will not be deployed, use only if you're
///         // sure you don't need them.
///         // contract and alice still need to be manually instantiated.
///         let contract = Contract::<Erc20>::from_tag("contract");
///         let alice = Address::from_tag("alice");
///
///         // ...
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn test(attr: TokenStream, input: TokenStream) -> TokenStream {
    test::test(&attr, input)
}
