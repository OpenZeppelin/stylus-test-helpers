//! Defines the `#[motsu::test]` procedural macro.
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, FnArg};

/// Defines a unit test that provides access to Stylus execution context.
///
/// For more information see [`crate::test`].
pub(crate) fn test(_attr: &TokenStream, input: TokenStream) -> TokenStream {
    let item_fn = parse_macro_input!(input as syn::ItemFn);
    let attrs = &item_fn.attrs;
    let sig = &item_fn.sig;
    let fn_name = &sig.ident;
    let fn_return_type = &sig.output;
    let fn_block = &item_fn.block;
    let fn_args = &sig.inputs;

    // Whether 1 or none contracts will be declared.
    let arg_binding_and_ty = match fn_args
        .into_iter()
        .map(|arg| {
            let FnArg::Typed(arg) = arg else {
                error!(@arg, "unexpected receiver argument in test signature");
            };
            let arg_binding = &arg.pat;
            let arg_ty = &arg.ty;
            Ok((arg_binding, arg_ty))
        })
        .collect::<Result<Vec<_>, _>>()
    {
        Ok(res) => res,
        Err(err) => return err.to_compile_error().into(),
    };

    // Collect argument definitions.
    let arg_defs = arg_binding_and_ty.iter().map(|(arg_binding, arg_ty)| {
        quote! {
            #arg_binding: #arg_ty
        }
    });

    // Collect argument initializations.
    let arg_inits = arg_binding_and_ty.iter().map(|(arg_binding, arg_ty)| {
        quote! {
            <#arg_ty as motsu::prelude::DeriveFromTag>::from_tag(stringify!(#arg_binding))
        }
    });

    // Declare test case closure.
    // Pass arguments to the test closure and call it.
    quote! {
        #( #attrs )*
        #[test]
        fn #fn_name() #fn_return_type {
            let test = | #( #arg_defs ),* | #fn_block;
            test( #( #arg_inits ),* )
        }
    }
    .into()
}
