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
pub(crate) mod wrapping;

/// Define a signed integer.
///
/// Sample use is:
///
/// ```rust,ignore
/// crate::int::define!(
///     name => i256,
///     unsigned_t => crate::u256,
///     unsigned_wide_t => u128,
///     signed_wide_t => i128,
///     bits => 256,
/// );
/// ```
macro_rules! define {
    (
        name => $name:ident,
        unsigned_t => $u_t:ty,
        unsigned_wide_t => $wide_u_t:ty,
        signed_wide_t => $wide_s_t:ty,
        bits => $bits:expr  $(,)?
    ) => {
        $crate::shared::int_struct_define!(
            name => $name,
            bits => $bits,
            kind => signed,
        );

        impl $name {
            $crate::int::constants::define!(
                bits => $bits,
                wide_type => $wide_s_t,
            );
            $crate::int::bitops::define!(unsigned_type => $u_t, wide_type => $wide_s_t);
            $crate::shared::endian::define!(type => $u_t, wide_type => $wide_s_t);
            $crate::shared::ord::define!(
                low_type => $wide_u_t,
                high_type => $wide_s_t,
            );
            $crate::int::casts::define!(
                unsigned_type => $u_t,
                bits => $bits,
                wide_type => $wide_s_t,
                kind => signed,
            );
            $crate::shared::extensions::define!(high_type => $crate::ILimb);
            $crate::int::ops::define!(unsigned_type => $u_t, wide_type => $wide_s_t);
            $crate::shared::bigint::define!(wide_type => $wide_s_t);
            $crate::int::wrapping::define!(unsigned_type => $u_t, wide_type => $wide_s_t);
            $crate::int::overflowing::define!(unsigned_type => $u_t, wide_type => $wide_s_t);
            $crate::int::saturating::define!(unsigned_type => $u_t, wide_type => $wide_s_t);
            $crate::int::checked::define!(unsigned_type => $u_t, wide_type => $wide_s_t);
            $crate::int::strict::define!(unsigned_type => $u_t, wide_type => $wide_s_t);
            $crate::shared::unchecked::define!(type => $u_t, wide_type => $wide_s_t);
            $crate::shared::unbounded::define!(type => $u_t, wide_type => $wide_s_t);
            $crate::int::limb::define!(@all);

            $crate::parse::define!(true);
            $crate::write::define!(true);
        }

        $crate::int::traits::define!(type => $name, unsigned_type => $u_t);
    };
}

pub(crate) use define;