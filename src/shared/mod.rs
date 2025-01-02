//! Shared macros between big and small integers.
//! Macros shared between signed and unsigned types.

// FIXME: Add support for [Saturating][core::num::Saturating] and
// [Wrapping][core::num::Wrapping] when we drop support for <1.74.0.

pub(crate) mod bigint;
pub(crate) mod bitops;
pub(crate) mod casts;
pub(crate) mod checked;
pub(crate) mod constants;
pub(crate) mod docs;
pub(crate) mod endian;
pub(crate) mod extensions;
pub(crate) mod limb;
pub(crate) mod ops;
pub(crate) mod ord;
pub(crate) mod overflowing;
pub(crate) mod saturating;
pub(crate) mod shift;
pub(crate) mod strict;
pub(crate) mod traits;
pub(crate) mod unbounded;
pub(crate) mod unchecked;
pub(crate) mod wrapping;

// FIXME: Add support for [Saturating][core::num::Saturating] and
// [Wrapping][core::num::Wrapping] when we drop support for <1.74.0.

#[rustfmt::skip]
macro_rules! int_struct_define {
    (
        $(#[$attr:meta])?
        name => $name:ident,
        bits => $bits:literal,
        kind => $kind:ident $(,)?
    ) => {
        #[rustfmt::skip]
        #[doc = concat!("The ", stringify!($bits), "-bit ", stringify!($kind), " integer type.")]
        ///
        /// The high and low words depend on the target endianness.
        /// Conversion to and from big endian should be done via
        /// [`to_le_bytes`] and [`to_be_bytes`].
        ///
        /// Our formatting specifications are limited: we ignore a
        /// lot of settings, and only respect [`alternate`] among the
        /// formatter flags. So, we implement all the main formatters
        /// ([`Binary`], etc.), but ignore all flags like `width`.
        ///
        /// Note that this type is **NOT** safe to use in FFIs, since the
        /// underlying storage may use [`128-bit`] integers in the future
        /// which are not FFI-safe. If you would like to use this type
        /// within a FFI, use [`to_le_bytes`] and [`to_be_bytes`].
        ///
        #[doc = concat!("[`to_le_bytes`]: ", stringify!($name), "::to_le_bytes")]
        #[doc = concat!("[`to_be_bytes`]: ", stringify!($name), "::to_be_bytes")]
        $(#[$attr])?
        /// [`alternate`]: core::fmt::Formatter::alternate
        /// [`Binary`]: core::fmt::Binary
        /// [`128-bit`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
        pub struct $name {
            // NOTE: This is currently FFI-safe (if we did repr(C)) but we
            // intentionally make  no guarantees so we're free to re-arrange
            // the layout.
            limbs: [$crate::ULimb; $bits / core::mem::size_of::<$crate::ULimb>() / 8],
        }
    };
}

pub(crate) use int_struct_define;
