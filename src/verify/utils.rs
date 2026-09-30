use std::format;
use std::string::String;

use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAnyhowError(anyhow::Error);

pub assume_specification<M: core::fmt::Display + core::fmt::Debug + Send + Sync + 'static>[
    anyhow::Error::msg::<M>
](message: M) -> (error: anyhow::Error);

pub assume_specification<'a>[
    anyhow::__private::format_err
](args: core::fmt::Arguments<'a>) -> (error: anyhow::Error);

pub assume_specification[
    anyhow::__private::must_use
](error: anyhow::Error) -> (result: anyhow::Error);

// vstd doesn't specify `to_ascii_uppercase`, and callers don't rely on its
// result, so this promises nothing.
pub assume_specification[ <str>::to_ascii_uppercase ](s: &str) -> (res: String);

} // end verus!
