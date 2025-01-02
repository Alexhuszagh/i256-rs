//! Signed big integer types integer type.
//!
//! This aims to have feature parity with Rust's signed
//! integer types, such as [i32][core::i32]. The documentation
//! is based off of [i32][core::i32] for each method/member.
//!
//! Rust's signed integers are guaranteed to be [`two's complement`],
//! so we guarantee the same representation internally.
//!
//! [`two's complement`]: https://en.wikipedia.org/wiki/Two%27s_complement
//!
//! A large portion of the implementation for helper functions
//! are based off of the Rust core implementation, such as for
//! [`checked_pow`][i128::checked_pow], [`isqrt`][i128::isqrt],
//! and more. Any non-performance critical functions, or those
//! crucial to parsing or serialization ([`add`][`i256::add`],
//! [`mul`][`i256::mul`], [`div`][`i256::div`], and
//! [`sub`][`i256::sub`]), as well as their `wrapping_*`,
//! `checked_*`, `overflowing_*` and `*_wide` variants are
//! likely based on the core implementations.

pub(crate) mod bitops;
pub(crate) mod casts;
pub(crate) mod checked;
pub(crate) mod constants;
pub(crate) mod limb;
pub(crate) mod ops;
pub(crate) mod overflowing;
pub(crate) mod saturating;
pub(crate) mod strict;
pub(crate) mod traits;
pub(crate) mod unchecked;
pub(crate) mod wrapping;

/// Define a signed integer.
///
/// Sample use is:
///
/// ```rust,ignore
/// crate::int::define!(
///     name => i256,
///     unsigned_t => crate::u256,
///     bits => 256,
/// );
/// ```
macro_rules! define {
    (
        $(#[$attr:meta])?
        name => $name:ident,
        unsigned_t => $u_t:ty,
        bits => $bits:expr  $(,)?
    ) => {
        $crate::shared::int_struct_define!(
            $(#[$attr])?
            name => $name,
            bits => $bits,
            kind => signed,
        );

        impl $name {
            $crate::int::constants::define!(
                bits => $bits,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::int::bitops::define!(
                unsigned_type => $u_t,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::shared::endian::define!(
                type => $u_t,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::shared::ord::define!(
                low_type => $crate::UWide,
                high_type => $crate::IWide,
            );
            $crate::int::casts::define!(
                unsigned_type => $u_t,
                bits => $bits,
                see_type => i64,
                kind => signed,
            );
            $crate::shared::extensions::define!(
                high_type => $crate::ILimb,
            );
            $crate::int::ops::define!(
                unsigned_type => $u_t,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::shared::bigint::define!(
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::int::wrapping::define!(
                unsigned_type => $u_t,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::int::overflowing::define!(
                unsigned_type => $u_t,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::int::saturating::define!(
                unsigned_type => $u_t,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::int::checked::define!(
                unsigned_type => $u_t,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::int::strict::define!(
                unsigned_type => $u_t,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::int::unchecked::define!(
                unsigned_type => $u_t,
                wide_type => $crate::IWide,
                see_type => i64,
            );
            $crate::shared::unbounded::define!(
                type => $u_t,
                wide_type => $crate::IWide,
            );
            $crate::int::limb::define!(@all);

            $crate::parse::define!(true);
            $crate::write::define!(true);
        }

        $crate::int::traits::define!(type => $name, unsigned_type => $u_t);
    };
}

pub(crate) use define;
