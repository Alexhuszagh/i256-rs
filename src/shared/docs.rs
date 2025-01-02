//! Additional, miscellaneous docstrings.

#[rustfmt::skip]
macro_rules! nightly_doc {
    () => {
"
<div class=\"warning\">

This is a nightly-only experimental API in the Rust core implementation,
and therefore is subject to change at any time.
</div>
"
    };
}

pub(crate) use nightly_doc;

#[rustfmt::skip]
macro_rules! primitive_doc {
    ($t:ty, $func:ident) => {
        concat!("See [`", stringify!($t), "::", stringify!($func),"`].")
    };
}

pub(crate) use primitive_doc;

#[rustfmt::skip]
macro_rules! strict_doc {
    () => {
"
## Overflow behavior

This function will always panic on overflow, regardless of whether
overflow checks are enabled.
"
    };

    (panics) => {
        concat!("# Panics\n\n", $crate::shared::docs::strict_doc!())
    };

    (div-zero) => {
        concat!(
            $crate::shared::docs::div_by_zero_doc!(),
            "\n\n",
            $crate::shared::docs::strict_doc!()
        )
    };
}

pub(crate) use strict_doc;

macro_rules! div_by_zero_doc {
    () => {
        $crate::shared::docs::div_by_zero_doc!(rhs)
    };

    ($arg:ident) => {
        concat!("# Panics\n\nThis function will panic if `", stringify!($arg), "` is zero.")
    };
}

pub(crate) use div_by_zero_doc;

macro_rules! div_by_zero_signed_doc {
    () => {
        $crate::shared::docs::div_by_zero_signed_doc!(rhs)
    };

    ($arg:ident) => {
        concat!("# Panics\n\nThis function will panic if `", stringify!($arg), "` is zero or if `self` is `Self::MIN` and `rhs` is -1.  This behavior is not affected by the `overflow-checks` flag.")
    };
}

pub(crate) use div_by_zero_signed_doc;

#[rustfmt::skip]
macro_rules! unchecked_doc {
    () => {
"
# Safety

This results in undefined behavior when the value overflows.
"
    };
}

pub(crate) use unchecked_doc;

#[rustfmt::skip]
macro_rules! must_use_copy_doc {
    () => {
        "this returns the result of the operation, without modifying the original"
    };
}

pub(crate) use must_use_copy_doc;

#[rustfmt::skip]
macro_rules! overflow_assertions_doc {
    () => {
"
## Overflow behavior

On overflow, this function will panic if overflow checks are enabled
(default in debug mode) and wrap if overflow checks are disabled
(default in release mode).
"
    };
}

pub(crate) use overflow_assertions_doc;

#[rustfmt::skip]
macro_rules! fixed_doc {
    ($op:ident) => {
        concat!(
"
This allows optimizations a full ", stringify!($op), " cannot do.
"
)
    };
}

pub(crate) use fixed_doc;

#[rustfmt::skip]
macro_rules! limb_doc {
    ($op:ident) => {
        concat!(
"
This allows optimizations a full ", stringify!($op), " cannot do.

Please note that the size of [`ULimb`] depends on the target architecture and
can be 64 or 128 bits large. If you need support for scalars of a guaranteed
width, use the `*_u32`, `_u64`, and `_u128` APIs instead, such as
[`u256::add_u32`] (requires the `stdint` feature).
"
)
    };
}

pub(crate) use limb_doc;

#[rustfmt::skip]
macro_rules! wide_doc {
    ($op:ident) => {
        concat!(
"
This allows may allows optimizations a full ", stringify!($op), " cannot do.
However, performance can be highly variable and you should always benchmark
your results. A full description of the performance tradeoffs with wide types
can be found in the documentation for [`UWide`][crate::UWide].

Please note that the size of [`UWide`] depends on the target architecture and
can be 64 or 128 bits large. If you need support for scalars of a guaranteed
width, use the `*_u32`, `_u64`, and `_u128` APIs instead, such as
[`u256::add_u32`] (requires the `stdint` feature).
"
        )
    };
}

pub(crate) use wide_doc;

#[rustfmt::skip]
macro_rules! as_cast_doc {
    (
        $bits:literal,
        $kind:ident,
        $to:expr $(,)?
    ) => {
        concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " integer to ", $to, ", as if by an `as` cast.")
    };
}

pub(crate) use as_cast_doc;

#[rustfmt::skip]
macro_rules! from_cast_doc {
    (
        $bits:literal,
        $kind:ident,
        $to:expr $(,)?
    ) => {
        concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from ", $to, ", as if by an `as` cast.")
    };
}

pub(crate) use from_cast_doc;
