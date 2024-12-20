//! An unsigned 256-bit integer type.
//!
//! This aims to have feature parity with Rust's unsigned
//! integer types, such as [u32][core::u32]. The documentation
//! is based off of [u32][core::u32] for each method/member.
//!
//! A large portion of the implementation for helper functions
//! are based off of the Rust core implementation, such as for
//! [`checked_pow`][u128::checked_pow], [`isqrt`][u128::isqrt],
//! and more. Any non-performance critical functions, or those
//! crucial to parsing or serialization ([`add`][`u256::add`],
//! [`mul`][`u256::mul`], [`div`][`u256::div`], and
//! [`sub`][`u256::sub`]), as well as their `wrapping_*`,
//! `checked_*`, `overflowing_*` and `*_small` variants are
//! likely based on the core implementations.

use core::cmp::Ordering;
use core::str::{FromStr, Utf8Error};
use core::{fmt, mem, str};
use core::{ops::*, panic};

use crate::error::{IntErrorKind, ParseIntError, TryFromIntError};
use crate::i256;
use crate::math;
use crate::numtypes::*;

// FIXME: Add support for [Saturating][core::num::Saturating] and
// [Wrapping][core::num::Wrapping] when we drop support for <1.74.0.

/// The 256-bit unsigned integer type.
///
/// The high and low words depend on the target endianness.
/// Conversion to and from big endian should be done via
/// [`to_le_bytes`] and [`to_be_bytes`]. or using
/// [`get_high`] and [`get_low`]. This is stored
/// as if it were a native, unsigned integer.
///
/// Our formatting specifications are limited: we ignore a
/// lot of settings, and only respect [`alternate`] among the
/// formatter flags. So, we implement all the main formatters
/// ([`Binary`], etc.), but ignore all flags like `width`.
///
/// Note that this type is **NOT** safe in FFIs, since it uses
/// [`128-bit`] integers under the hood which are implementation-
/// defined and not FFI-safe. If you would like to use convert
/// this to an FFI, use [`to_le_bytes`] and [`to_be_bytes`].
///
/// [`to_le_bytes`]: i256::to_le_bytes
/// [`to_be_bytes`]: i256::to_be_bytes
/// [`get_high`]: i256::get_high
/// [`get_low`]: i256::get_low
/// [`alternate`]: fmt::Formatter::alternate
/// [`Binary`]: fmt::Binary
/// [`128-bit`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
#[cfg(target_endian = "little")]
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
pub struct u256 {
    pub(crate) lo: u128,
    pub(crate) hi: u128,
}

/// The 256-bit unsigned integer type.
///
/// The high and low words depend on the target endianness.
/// Conversion to and from big endian should be done via
/// [`to_le_bytes`] and [`to_be_bytes`]. or using
/// [`get_high`] and [`get_low`]. This is stored
/// as if it were a native, unsigned integer.
///
/// Our formatting specifications are limited: we ignore a
/// lot of settings, and only respect [`alternate`] among the
/// formatter flags. So, we implement all the main formatters
/// ([`Binary`], etc.), but ignore all flags like `width`.
///
/// Note that this type is **NOT** safe in FFIs, since it uses
/// [`128-bit`] integers under the hood which are implementation-
/// defined and not FFI-safe. If you would like to use convert
/// this to an FFI, use [`to_le_bytes`] and [`to_be_bytes`].
///
/// [`to_le_bytes`]: i256::to_le_bytes
/// [`to_be_bytes`]: i256::to_be_bytes
/// [`get_high`]: i256::get_high
/// [`get_low`]: i256::get_low
/// ['alternate`]: fmt::Formatter::alternate
/// [`Binary`]: fmt::Binary
/// [`128-bit`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
#[cfg(target_endian = "big")]
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
pub struct u256 {
    pub(crate) hi: u128,
    pub(crate) lo: u128,
}

impl u256 {
    /// The smallest value that can be represented by this integer type.
    pub const MIN: Self = Self::new(0, 0);

    /// The largest value that can be represented by this integer type
    /// (2<sup>256</sup> - 1).
    pub const MAX: Self = Self::new(u128::MAX, u128::MAX);

    /// The size of this integer type in bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use i256::u256;
    /// assert_eq!(u256::BITS, 256);
    /// ```
    pub const BITS: u32 = 256;

    /// Returns the number of ones in the binary representation of `self`.
    #[inline(always)]
    pub const fn count_ones(self) -> u32 {
        self.hi.count_ones() + self.lo.count_ones()
    }

    /// Returns the number of zeros in the binary representation of `self`.
    #[inline(always)]
    pub const fn count_zeros(self) -> u32 {
        not(self).count_ones()
    }

    /// Returns the number of leading zeros in the binary representation of
    /// `self`.
    ///
    /// Depending on what you're doing with the value, you might also be
    /// interested in the `ilog2` function which returns a consistent
    /// number, even if the type widens.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use i256::u256;
    /// let n = u256::MAX >> 2i32;
    /// assert_eq!(n.leading_zeros(), 2);
    ///
    /// let zero = u256::MIN;
    /// assert_eq!(zero.leading_zeros(), 256);
    ///
    /// let max = u256::MAX;
    /// assert_eq!(max.leading_zeros(), 0);
    /// ```
    #[inline(always)]
    pub const fn leading_zeros(self) -> u32 {
        let mut leading = self.hi.leading_zeros();
        if leading == u128::BITS {
            leading += self.lo.leading_zeros();
        }
        leading
    }

    /// Returns the number of trailing zeros in the binary representation of
    /// `self`.
    #[inline(always)]
    pub const fn trailing_zeros(self) -> u32 {
        let mut trailing = self.hi.trailing_zeros();
        if trailing == u128::BITS {
            trailing += self.lo.trailing_zeros();
        }
        trailing
    }

    /// Returns the number of leading ones in the binary representation of
    /// `self`.
    #[inline(always)]
    pub const fn leading_ones(self) -> u32 {
        not(self).leading_zeros()
    }

    /// Returns the number of trailing ones in the binary representation of
    /// `self`.
    #[inline(always)]
    pub const fn trailing_ones(self) -> u32 {
        not(self).trailing_zeros()
    }

    /// Shifts the bits to the left by a specified amount, `n`,
    /// wrapping the truncated bits to the end of the resulting integer.
    ///
    /// Please note this isn't the same operation as the `<<` shifting operator!
    #[inline(always)]
    pub const fn rotate_left(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_left_u128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Shifts the bits to the right by a specified amount, `n`,
    /// wrapping the truncated bits to the beginning of the resulting
    /// integer.
    ///
    /// Please note this isn't the same operation as the `>>` shifting operator!
    #[inline(always)]
    pub const fn rotate_right(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_right_u128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Reverses the byte order of the integer.
    #[inline(always)]
    pub const fn swap_bytes(self) -> Self {
        let (lo, hi) = math::swap_bytes_u128(self.lo, self.hi);
        Self::new(lo, hi)
    }

    /// Reverses the order of bits in the integer. The least significant
    /// bit becomes the most significant bit, second least-significant bit
    /// becomes second most-significant bit, etc.
    #[inline(always)]
    pub const fn reverse_bits(self) -> Self {
        let (lo, hi) = math::reverse_bits_u128(self.lo, self.hi);
        Self::new(lo, hi)
    }

    /// Converts an integer from big endian to the target's endianness.
    ///
    /// On big endian this is a no-op. On little endian the bytes are
    /// swapped.
    #[inline(always)]
    pub const fn from_be(x: Self) -> Self {
        if cfg!(target_endian = "big") {
            x
        } else {
            x.swap_bytes()
        }
    }

    /// Converts an integer from little endian to the target's endianness.
    ///
    /// On little endian this is a no-op. On big endian the bytes are
    /// swapped.
    #[inline(always)]
    pub const fn from_le(x: Self) -> Self {
        if cfg!(target_endian = "little") {
            x
        } else {
            x.swap_bytes()
        }
    }

    /// Converts `self` to big endian from the target's endianness.
    ///
    /// On big endian this is a no-op. On little endian the bytes are
    /// swapped.
    #[inline(always)]
    pub const fn to_be(self) -> Self {
        if cfg!(target_endian = "big") {
            self
        } else {
            self.swap_bytes()
        }
    }

    /// Converts `self` to little endian from the target's endianness.
    ///
    /// On little endian this is a no-op. On big endian the bytes are
    /// swapped.
    #[inline(always)]
    pub const fn to_le(self) -> Self {
        if cfg!(target_endian = "little") {
            self
        } else {
            self.swap_bytes()
        }
    }

    /// Checked integer addition. Computes `self + rhs`, returning `None`
    /// if overflow occurred.
    #[inline(always)]
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked addition with a signed integer. Computes `self + rhs`,
    /// returning `None` if overflow occurred.
    #[inline(always)]
    pub const fn checked_add_signed(self, rhs: i256) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add_signed(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning `None`
    /// if overflow occurred.
    #[inline(always)]
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning `None`
    /// if overflow occurred.
    #[inline(always)]
    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked integer division. Computes `self / rhs`, returning `None`
    /// if `rhs == 0`.
    #[inline(always)]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        if eq(rhs, Self::MIN) {
            None
        } else {
            Some(self.wrapping_div(rhs))
        }
    }

    /// Performs Euclidean division.
    ///
    /// Since, for the positive integers, all common
    /// definitions of division are equal, this
    /// is exactly equal to `self / rhs`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn div_euclid(self, rhs: Self) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_euclid(rhs)
        } else {
            self.checked_div_euclid(rhs).expect("attempt to divide with overflow")
        }
    }

    /// Checked Euclidean division. Computes `self.div_euclid(rhs)`,
    /// returning `None` if `rhs == 0`.
    #[inline(always)]
    pub fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
        if eq(rhs, Self::MIN) {
            None
        } else {
            Some(self.wrapping_div_euclid(rhs))
        }
    }

    /// Checked integer division. Computes `self % rhs`, returning `None`
    /// if `rhs == 0`.
    #[inline(always)]
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        if eq(rhs, Self::MIN) {
            None
        } else {
            Some(self.wrapping_rem(rhs))
        }
    }

    /// Calculates the least remainder of `self (mod rhs)`.
    ///
    /// Since, for the positive integers, all common
    /// definitions of division are equal, this
    /// is exactly equal to `self % rhs`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn rem_euclid(self, rhs: Self) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_rem(rhs)
        } else {
            self.checked_rem_euclid(rhs).expect("attempt to divide by zero")
        }
    }

    /// Checked Euclidean modulo. Computes `self.rem_euclid(rhs)`,
    /// returning `None` if `rhs == 0`.
    #[inline(always)]
    pub fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
        if eq(rhs, Self::MIN) {
            None
        } else {
            Some(self.wrapping_rem_euclid(rhs))
        }
    }

    /// Returns the logarithm of the number with respect to an arbitrary base,
    /// rounded down.
    ///
    /// This method might not be optimized owing to implementation details;
    /// `ilog2` can produce results more efficiently for base 2, and `ilog10`
    /// can produce results more efficiently for base 10.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is zero, or if `base` is less than 2.
    #[inline(always)]
    pub fn ilog(self, base: Self) -> u32 {
        if let Some(log) = self.checked_ilog(base) {
            log
        } else {
            panic!("argument of integer logarithm must be positive")
        }
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is zero.
    #[inline(always)]
    pub const fn ilog2(self) -> u32 {
        if let Some(log) = self.checked_ilog2() {
            log
        } else {
            panic!("argument of integer logarithm must be positive")
        }
    }

    // FIXME: Stabilize when our MSRV goes to `1.67.0+`.
    // /// Returns the base 10 logarithm of the number, rounded down.
    // ///
    // /// # Panics
    // ///
    // /// This function will panic if `self` is zero.
    // #[inline(always)]
    // pub fn ilog10(self) -> u32 {
    //     if let Some(log) = self.checked_ilog10() {
    //         log
    //     } else {
    //         panic!("argument of integer logarithm must be positive")
    //     }
    // }

    /// Returns the logarithm of the number with respect to an arbitrary base,
    /// rounded down.
    ///
    /// Returns `None` if the number is zero, or if the base is not at least 2.
    ///
    /// This method might not be optimized owing to implementation details;
    /// `checked_ilog2` can produce results more efficiently for base 2, and
    /// `checked_ilog10` can produce results more efficiently for base 10.
    #[inline(always)]
    pub fn checked_ilog(self, base: Self) -> Option<u32> {
        let zero = Self::from_u8(0);
        if self == zero || base <= zero || lt(self, base) {
            return None;
        }

        // Since base >= self, n >= 1
        let mut n = 1;
        let mut r = base;

        // Optimization for 128+ bit wide integers.
        if Self::BITS >= 128 {
            // The following is a correct lower bound for ⌊log(base,self)⌋ because
            //
            // log(base,self) = log(2,self) / log(2,base)
            //                ≥ ⌊log(2,self)⌋ / (⌊log(2,base)⌋ + 1)
            //
            // hence
            //
            // ⌊log(base,self)⌋ ≥ ⌊ ⌊log(2,self)⌋ / (⌊log(2,base)⌋ + 1) ⌋ .
            n = self.ilog2() / (base.ilog2() + 1);
            r = base.pow(n);
        }

        while r <= self / base {
            n += 1;
            r *= base;
        }
        Some(n)
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// Returns `None` if the number is zero.
    #[inline(always)]
    pub const fn checked_ilog2(self) -> Option<u32> {
        match eq(self, Self::from_u8(0)) {
            true => None,
            false => Some(Self::BITS - 1 - self.leading_zeros()),
        }
    }

    // FIXME: Stabilize when our MSRV goes to `1.67.0+`.
    // /// Returns the base 10 logarithm of the number, rounded down.
    // ///
    // /// Returns `None` if the number is zero.
    // #[inline(always)]
    // pub fn checked_ilog10(self) -> Option<u32> {
    //     match eq(self, Self::from_u8(0)) {
    //         true => None,
    //         false => {
    //             // NOTE: The `ilog10` implementations for small
    //             // numbers are quite efficient, so we use those
    //             // when available. We want to get this to
    //             // a 128-bit integer in as few multiplications
    //             // as we can.
    //             let mut log = 0;
    //             let mut value = self;
    //             const E16: u64 = 10_000_000_000_000_000;
    //             while value.hi > 0 {
    //                 value = value.div_small(E16);
    //                 log += 16;
    //             }
    //             let value: u128 = value.as_u128();
    //             Some(value.ilog10() + log)
    //         },
    //     }
    // }

    /// Checked negation. Computes `-self`, returning `None` unless `self ==
    /// 0`.
    ///
    /// Note that negating any positive integer will overflow.
    #[inline(always)]
    pub const fn checked_neg(self) -> Option<Self> {
        if eq(self, Self::MIN) {
            Some(self)
        } else {
            None
        }
    }

    /// Checked shift left. Computes `self << rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    #[inline(always)]
    pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
        if rhs < Self::BITS {
            Some(self.shl_u32(rhs))
        } else {
            None
        }
    }

    /// Checked shift right. Computes `self >> rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    #[inline(always)]
    pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
        if rhs < Self::BITS {
            Some(self.shr_u32(rhs))
        } else {
            None
        }
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None`
    /// if overflow occurred.
    #[inline(always)]
    pub const fn checked_pow(self, base: u32) -> Option<Self> {
        match self.overflowing_pow(base) {
            (value, false) => Some(value),
            _ => None,
        }
    }

    /// Saturating integer addition. Computes `self + rhs`, saturating at
    /// the numeric bounds instead of overflowing.
    #[inline(always)]
    pub const fn saturating_add(self, rhs: Self) -> Self {
        match self.checked_add(rhs) {
            Some(v) => v,
            None => Self::MAX,
        }
    }

    /// Saturating addition with a signed integer. Computes `self + rhs`,
    /// saturating at the numeric bounds instead of overflowing.
    #[inline(always)]
    pub const fn saturating_add_signed(self, rhs: i256) -> Self {
        let is_negative = rhs.hi < 0;
        let (r, overflowed) = self.overflowing_add(Self::from_i256(rhs));
        if overflowed == is_negative {
            r
        } else if overflowed {
            Self::MAX
        } else {
            Self::MIN
        }
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating
    /// at the numeric bounds instead of overflowing.
    #[inline(always)]
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        match self.checked_sub(rhs) {
            Some(v) => v,
            None => Self::MAX,
        }
    }

    /// Saturating integer multiplication. Computes `self * rhs`,
    /// saturating at the numeric bounds instead of overflowing.
    #[inline(always)]
    pub const fn saturating_mul(self, rhs: Self) -> Self {
        match self.checked_mul(rhs) {
            Some(v) => v,
            None => Self::MAX,
        }
    }

    /// Saturating integer division. Computes `self / rhs`, saturating at the
    /// numeric bounds instead of overflowing.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn saturating_div(self, rhs: Self) -> Self {
        // on unsigned types, there is no overflow in integer division
        self.wrapping_div(rhs)
    }

    /// Saturating integer exponentiation. Computes `self.pow(exp)`,
    /// saturating at the numeric bounds instead of overflowing.
    #[inline]
    pub const fn saturating_pow(self, exp: u32) -> Self {
        match self.checked_pow(exp) {
            Some(x) => x,
            None => Self::MAX,
        }
    }

    /// Wrapping (modular) addition. Computes `self + rhs`,
    /// wrapping around at the boundary of the type.
    #[inline(always)]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        let (lo, hi, _) = math::add_u128(self.lo, self.hi, rhs.lo, rhs.hi);
        u256::new(lo, hi)
    }

    /// Wrapping (modular) addition with a signed integer. Computes
    /// `self + rhs`, wrapping around at the boundary of the type.
    #[inline(always)]
    pub const fn wrapping_add_signed(self, rhs: i256) -> Self {
        self.wrapping_add(Self::from_i256(rhs))
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`,
    /// wrapping around at the boundary of the type.
    #[inline(always)]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        let (lo, hi, _) = math::sub_u128(self.lo, self.hi, rhs.lo, rhs.hi);
        u256::new(lo, hi)
    }

    /// Wrapping (modular) multiplication. Computes `self *
    /// rhs`, wrapping around at the boundary of the type.
    #[inline(always)]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        let (lo, hi, _) = math::mul_u128(self.lo, self.hi, rhs.lo, rhs.hi);
        u256::new(lo, hi)
    }

    /// Wrapping (modular) division. Computes `self / rhs`.
    ///
    /// Wrapped division on unsigned types is just normal division. There's
    /// no way wrapping could ever happen. This function exists so that all
    /// operations are accounted for in the wrapping operations.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn wrapping_div(self, rhs: Self) -> Self {
        div_rem(self, rhs).0
    }

    /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`.
    ///
    /// Wrapped division on unsigned types is just normal division. There's
    /// no way wrapping could ever happen. This function exists so that all
    /// operations are accounted for in the wrapping operations. Since, for
    /// the positive integers, all common definitions of division are equal,
    /// this is exactly equal to `self.wrapping_div(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn wrapping_div_euclid(self, rhs: Self) -> Self {
        self.wrapping_div(rhs)
    }

    /// Wrapping (modular) remainder. Computes `self % rhs`.
    ///
    /// Wrapped remainder calculation on unsigned types is just the regular
    /// remainder calculation. There's no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the
    /// wrapping operations.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn wrapping_rem(self, rhs: Self) -> Self {
        div_rem(self, rhs).1
    }

    /// Wrapping Euclidean modulo. Computes `self.rem_euclid(rhs)`.
    ///
    /// Wrapped modulo calculation on unsigned types is just the regular
    /// remainder calculation. There's no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the
    /// wrapping operations. Since, for the positive integers, all common
    /// definitions of division are equal, this is exactly equal to
    /// `self.wrapping_rem(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn wrapping_rem_euclid(self, rhs: Self) -> Self {
        self.wrapping_rem(rhs)
    }

    /// Wrapping (modular) negation. Computes `-self`,
    /// wrapping around at the boundary of the type.
    ///
    /// Since unsigned types do not have negative equivalents
    /// all applications of this function will wrap (except for `-0`).
    /// For values smaller than the corresponding signed type's maximum
    /// the result is the same as casting the corresponding signed value.
    /// Any larger values are equivalent to `MAX + 1 - (val - MAX - 1)` where
    /// `MAX` is the corresponding signed type's maximum.
    #[inline(always)]
    pub const fn wrapping_neg(self) -> Self {
        Self::MIN.wrapping_sub(self)
    }

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-left; the
    /// RHS of a wrapping shift-left is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The primitive integer
    /// types all implement a [`rotate_left`](Self::rotate_left) function,
    /// which may be what you want instead.
    #[inline(always)]
    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        let (lo, hi) = math::shl_u128(self.lo, self.hi, rhs % 256);
        Self::new(lo, hi)
    }

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-right; the
    /// RHS of a wrapping shift-right is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The primitive integer
    /// types all implement a [`rotate_right`](Self::rotate_right) function,
    /// which may be what you want instead.
    #[inline(always)]
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        let (lo, hi) = math::shr_u128(self.lo, self.hi, rhs % 256);
        Self::new(lo, hi)
    }

    /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`,
    /// wrapping around at the boundary of the type.
    #[inline]
    pub const fn wrapping_pow(self, mut exp: u32) -> Self {
        if exp == 0 {
            return Self::from_u8(1);
        }
        let mut base = self;
        let mut acc = Self::from_u8(1);

        // NOTE: The exponent can never go to 0.
        loop {
            if (exp & 1) == 1 {
                acc = acc.wrapping_mul(base);
                // since exp!=0, finally the exp must be 1.
                if exp == 1 {
                    return acc;
                }
            }
            exp /= 2;
            base = base.wrapping_mul(base);
            debug_assert!(exp != 0, "logic error in exponentiation, will infinitely loop");
        }
    }

    /// Calculates `self` + `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    #[inline(always)]
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) = math::add_u128(self.lo, self.hi, rhs.lo, rhs.hi);
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates `self` + `rhs` with a signed `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    #[inline(always)]
    pub const fn overflowing_add_signed(self, rhs: i256) -> (Self, bool) {
        let is_negative = rhs.hi < 0;
        let (r, overflowed) = self.overflowing_add(Self::from_i256(rhs));
        (r, overflowed ^ is_negative)
    }

    /// Calculates `self` - `rhs`.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    #[inline(always)]
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) = math::sub_u128(self.lo, self.hi, rhs.lo, rhs.hi);
        (Self::new(lo, hi), overflowed)
    }

    /// Computes the absolute difference between `self` and `other`.
    #[inline(always)]
    pub const fn abs_diff(self, other: Self) -> Self {
        if lt(self, other) {
            other.wrapping_sub(self)
        } else {
            self.wrapping_sub(other)
        }
    }

    /// Calculates the multiplication of `self` and `rhs`.
    ///
    /// Returns a tuple of the multiplication along with a boolean
    /// indicating whether an arithmetic overflow would occur. If an
    /// overflow would have occurred then the wrapped value is returned.
    #[inline(always)]
    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) = math::mul_u128(self.lo, self.hi, rhs.lo, rhs.hi);
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates the divisor when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating
    /// whether an arithmetic overflow would occur. Note that for unsigned
    /// integers overflow never occurs, so the second value is always
    /// `false`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn overflowing_div(self, rhs: Self) -> (Self, bool) {
        // TODO: Fix this
        (self.wrapping_div(rhs), false)
    }

    /// Calculates the quotient of Euclidean division `self.div_euclid(rhs)`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating
    /// whether an arithmetic overflow would occur. Note that for unsigned
    /// integers overflow never occurs, so the second value is always
    /// `false`.
    /// Since, for the positive integers, all common
    /// definitions of division are equal, this
    /// is exactly equal to `self.overflowing_div(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
        self.overflowing_div(rhs)
    }

    /// Calculates the remainder when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the remainder after dividing along with a boolean
    /// indicating whether an arithmetic overflow would occur. Note that for
    /// unsigned integers overflow never occurs, so the second value is
    /// always `false`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
        // TODO: Fix this
        (self.wrapping_rem(rhs), false)
    }

    /// Calculates the remainder `self.rem_euclid(rhs)` as if by Euclidean
    /// division.
    ///
    /// Returns a tuple of the modulo after dividing along with a boolean
    /// indicating whether an arithmetic overflow would occur. Note that for
    /// unsigned integers overflow never occurs, so the second value is
    /// always `false`.
    /// Since, for the positive integers, all common
    /// definitions of division are equal, this operation
    /// is exactly equal to `self.overflowing_rem(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
        self.overflowing_rem(rhs)
    }

    /// Raises self to the power of `exp`, using exponentiation by squaring.
    ///
    /// Returns a tuple of the exponentiation along with a bool indicating
    /// whether an overflow happened.
    #[inline]
    pub const fn overflowing_pow(self, mut exp: u32) -> (Self, bool) {
        if exp == 0 {
            return (Self::from_u8(1), false);
        }
        let mut base = self;
        let mut acc = Self::from_u8(1);
        let mut overflown = false;
        let mut r: (Self, bool);

        // NOTE: The exponent can never go to 0.
        loop {
            if (exp & 1) == 1 {
                r = acc.overflowing_mul(base);
                // since exp!=0, finally the exp must be 1.
                if exp == 1 {
                    r.1 |= overflown;
                    return r;
                }
                acc = r.0;
                overflown |= r.1;
            }
            exp /= 2;
            r = base.overflowing_mul(base);
            base = r.0;
            overflown |= r.1;
            debug_assert!(exp != 0, "logic error in exponentiation, will infinitely loop");
        }
    }

    /// Raises self to the power of `exp`, using exponentiation by squaring.
    #[inline]
    pub const fn pow(self, exp: u32) -> Self {
        // FIXME: If #111466 is stabilized, we can use that
        // and determine if overflow checks are enabled.
        self.wrapping_pow(exp)
    }

    // FIXME: Stabilize when our MSRV goes to `1.84.0+`.
    // /// Returns the square root of the number, rounded down.
    // #[inline]
    // pub const fn isqrt(self) -> Self {
    //     todo!();
    // }

    /// Calculates the quotient of `self` and `rhs`, rounding the result towards
    /// negative infinity.
    ///
    /// This is the same as performing `self / rhs` for all unsigned integers.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn div_floor(self, rhs: Self) -> Self {
        self.wrapping_div(rhs)
    }

    /// Calculates the quotient of `self` and `rhs`, rounding the result towards
    /// positive infinity.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    #[inline(always)]
    pub fn div_ceil(self, rhs: Self) -> Self {
        let (d, r) = div_rem(self, rhs);
        if r.lo > 0 || r.hi > 0 {
            let (lo, hi, _) = math::add_u128(d.lo, d.hi, 1, 0);
            Self::new(lo, hi)
        } else {
            d
        }
    }

    /// Calculates the smallest value greater than or equal to `self` that
    /// is a multiple of `rhs`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// ## Overflow behavior
    ///
    /// On overflow, this function will panic if overflow checks are enabled
    /// (default in debug mode) and wrap if overflow checks are disabled
    /// (default in release mode).
    #[inline]
    pub fn next_multiple_of(self, rhs: Self) -> Self {
        match self.wrapping_rem(rhs) {
            Self::MIN => self,
            r => self.wrapping_add(rhs.wrapping_sub(r)),
        }
    }

    /// Calculates the smallest value greater than or equal to `self` that
    /// is a multiple of `rhs`. Returns `None` if `rhs` is zero or the
    /// operation would result in overflow.
    #[inline]
    pub fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
        match self.checked_rem(rhs) {
            None => None,
            Some(Self::MIN) => Some(self),
            // rhs - r cannot overflow because r is smaller than rhs
            Some(r) => self.checked_add(rhs.wrapping_sub(r)),
        }
    }

    /// Returns `true` if `self` is an integer multiple of `rhs`, and false
    /// otherwise.
    ///
    /// This function is equivalent to `self % rhs == 0`, except that it will
    /// not panic for `rhs == 0`. Instead, `0.is_multiple_of(0) == true`,
    /// and for any non-zero `n`, `n.is_multiple_of(0) == false`.
    #[inline]
    pub fn is_multiple_of(self, rhs: Self) -> bool {
        match rhs {
            Self::MIN => eq(self, Self::MIN),
            _ => eq(self.wrapping_rem(rhs), Self::MIN),
        }
    }

    /// Returns `true` if and only if `self == 2^k` for some `k`.
    #[inline(always)]
    pub const fn is_power_of_two(self) -> bool {
        self.count_ones() == 1
    }

    #[inline]
    const fn one_less_than_next_power_of_two(self) -> Self {
        if eq(self, Self::MIN) {
            return Self::MIN;
        }
        let p = self.wrapping_sub(Self::from_u8(1));
        let z = p.leading_zeros();
        Self::MAX.shr_u32(z)
    }

    /// Returns the smallest power of two greater than or equal to `self`.
    ///
    /// When return value overflows (i.e., `self > (1 << (N-1))` for type
    /// `uN`), it panics in debug mode and the return value is wrapped to 0 in
    /// release mode (the only situation in which this method can return 0).
    #[inline]
    pub const fn next_power_of_two(self) -> Self {
        self.one_less_than_next_power_of_two().wrapping_add(Self::from_u8(1))
    }

    /// Returns the smallest power of two greater than or equal to `self`. If
    /// the next power of two is greater than the type's maximum value,
    /// `None` is returned, otherwise the power of two is wrapped in `Some`.
    #[inline]
    pub const fn checked_next_power_of_two(self) -> Option<Self> {
        self.one_less_than_next_power_of_two().checked_add(Self::from_u8(1))
    }

    /// Returns the memory representation of this integer as a byte array in
    /// big-endian (network) byte order.
    #[inline(always)]
    pub const fn to_be_bytes(self) -> [u8; 32] {
        self.to_be().to_ne_bytes()
    }

    /// Returns the memory representation of this integer as a byte array in
    /// little-endian byte order.
    #[inline(always)]
    pub const fn to_le_bytes(self) -> [u8; 32] {
        self.to_le().to_ne_bytes()
    }

    /// Returns the memory representation of this integer as a byte array in
    /// native byte order.
    ///
    /// As the target platform's native endianness is used, portable code
    /// should use [`to_be_bytes`] or [`to_le_bytes`], as appropriate,
    /// instead.
    ///
    /// [`to_be_bytes`]: Self::to_be_bytes
    /// [`to_le_bytes`]: Self::to_le_bytes
    #[inline(always)]
    pub const fn to_ne_bytes(self) -> [u8; 32] {
        // SAFETY: integers are plain old datatypes so we can always transmute them to
        // arrays of bytes
        unsafe { mem::transmute(self) }
    }

    /// Creates a native endian integer value from its representation
    /// as a byte array in big endian.
    #[inline(always)]
    pub const fn from_be_bytes(bytes: [u8; 32]) -> Self {
        Self::from_be(Self::from_ne_bytes(bytes))
    }

    /// Creates a native endian integer value from its representation
    /// as a byte array in little endian.
    pub const fn from_le_bytes(bytes: [u8; 32]) -> Self {
        Self::from_le(Self::from_ne_bytes(bytes))
    }

    /// Creates a native endian integer value from its memory representation
    /// as a byte array in native endianness.
    ///
    /// As the target platform's native endianness is used, portable code
    /// likely wants to use [`from_be_bytes`] or [`from_le_bytes`], as
    /// appropriate instead.
    ///
    /// [`from_be_bytes`]: Self::from_be_bytes
    /// [`from_le_bytes`]: Self::from_le_bytes
    #[inline(always)]
    pub const fn from_ne_bytes(bytes: [u8; 32]) -> Self {
        // SAFETY: integers are plain old datatypes so we can always transmute to them
        unsafe { mem::transmute(bytes) }
    }

    /// Converts a string slice in a given base to an integer.
    ///
    /// The string is expected to be an optional `+`
    /// sign followed by only digits. Leading and trailing non-digit characters
    /// (including whitespace) represent an error. Underscores (which are
    /// accepted in rust literals) also represent an error.
    ///
    /// Digits are a subset of these characters, depending on `radix`:
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// # Panics
    ///
    /// This function panics if `radix` is not in the range from 2 to 36.
    #[inline]
    pub const fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        if radix < 2 || radix > 36 {
            panic!("from_str_radix_int: must lie in the range `[2, 36]`");
        }
        if src.is_empty() {
            return Err(ParseIntError {
                kind: IntErrorKind::Empty,
            });
        }
        todo!();
    }
}

impl u256 {
    /// Create a new `u256` from the low and high bits.
    #[inline(always)]
    pub const fn new(lo: u128, hi: u128) -> Self {
        Self {
            lo,
            hi,
        }
    }

    /// Get the high 128 bits of the signed integer.
    #[inline(always)]
    pub const fn get_high(self) -> u128 {
        self.hi
    }

    /// Get the low 128 bits of the signed integer.
    #[inline(always)]
    pub const fn get_low(self) -> u128 {
        self.lo
    }

    /// Create the 256-bit unsigned integer to a `u8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u8(value: u8) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer from a `u16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u16(value: u16) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer from a `u32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u32(value: u32) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer from a `u64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u64(value: u64) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer from a `u128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_u128(value: u128) -> Self {
        let (lo, hi) = math::as_uwide_u128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit unsigned integer to an `i8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_i8(value: i8) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit unsigned integer from an `i16`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i16(value: i16) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit unsigned integer from an `i32`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i32(value: i32) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit unsigned integer from an `i64`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i64(value: i64) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit unsigned integer from an `i128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i128(value: i128) -> Self {
        let (lo, hi) = math::as_iwide_u128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit unsigned integer from an `i256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i256(value: i256) -> Self {
        value.as_u256()
    }

    /// Convert the 256-bit unsigned integer to an `u8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u8(&self) -> u8 {
        self.lo as u8
    }

    /// Convert the 256-bit unsigned integer to an `u16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u16(&self) -> u16 {
        self.lo as u16
    }

    /// Convert the 256-bit unsigned integer to an `u32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u32(&self) -> u32 {
        self.lo as u32
    }

    /// Convert the 256-bit unsigned integer to an `u64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u64(&self) -> u64 {
        self.lo as u64
    }

    /// Convert the 256-bit unsigned integer to an `u128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_u128(&self) -> u128 {
        math::as_unarrow_u128(self.lo, self.hi)
    }

    /// Convert the 256-bit unsigned integer to an `u256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_u256(&self) -> Self {
        *self
    }

    /// Convert the 256-bit unsigned integer to an `i8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i8(&self) -> i8 {
        self.as_i128() as i8
    }

    /// Convert the 256-bit unsigned integer to an `i16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i16(&self) -> i16 {
        self.as_i128() as i16
    }

    /// Convert the 256-bit unsigned integer to an `i32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i32(&self) -> i32 {
        self.as_i128() as i32
    }

    /// Convert the 256-bit unsigned integer to an `i64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i64(&self) -> i64 {
        self.as_i128() as i64
    }

    /// Convert the 256-bit unsigned integer to an `i128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_i128(&self) -> i128 {
        math::as_inarrow_u128(self.lo, self.hi)
    }

    /// Convert the 256-bit unsigned integer to an `i256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_i256(&self) -> i256 {
        let (lo, hi) = math::wide_cast_u128(self.lo, self.hi);
        i256::new(lo, hi)
    }

    /// Add the 256-bit integer by a small, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn add_small(self, n: u128) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_add_small(n)
        } else {
            match self.checked_add_small(n) {
                Some(v) => v,
                None => panic!("attempt to add with overflow"),
            }
        }
    }

    /// Add the 256-bit integer by a small, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn wrapping_add_small(self, n: u128) -> Self {
        let (lo, hi, _) = math::add_small_u128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Add the 256-bit integer by a small, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn overflowing_add_small(self, n: u128) -> (Self, bool) {
        let (lo, hi, overflowed) = math::add_small_u128(self.lo, self.hi, n);
        (Self::new(lo, hi), overflowed)
    }

    /// Add the 256-bit integer by a small, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn checked_add_small(self, n: u128) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add_small(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Subtract the 256-bit integer by a small, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn sub_small(self, n: u128) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_sub_small(n)
        } else {
            match self.checked_sub_small(n) {
                Some(v) => v,
                None => panic!("attempt to subtract with overflow"),
            }
        }
    }

    /// Subtract the 256-bit integer by a small, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn wrapping_sub_small(self, n: u128) -> Self {
        let (lo, hi, _) = math::sub_small_u128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Subtract the 256-bit integer by a small, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn overflowing_sub_small(self, n: u128) -> (Self, bool) {
        let (lo, hi, overflowed) = math::sub_small_u128(self.lo, self.hi, n);
        (Self::new(lo, hi), overflowed)
    }

    /// Subtract the 256-bit integer by a small, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn checked_sub_small(self, n: u128) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub_small(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Multiply the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn mul_small(self, n: u128) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul_small(n)
        } else {
            match self.checked_mul_small(n) {
                Some(v) => v,
                None => panic!("attempt to multiply with overflow"),
            }
        }
    }

    /// Multiply the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn wrapping_mul_small(self, n: u128) -> Self {
        let (lo, hi, _) = math::mul_small_u128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_small(self, n: u128) -> (Self, bool) {
        let (lo, hi, overflowed) = math::mul_small_u128(self.lo, self.hi, n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn checked_mul_small(self, n: u128) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul_small(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Div/Rem the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    /// This panics if the divisor is 0.
    #[inline(always)]
    pub fn div_rem_small(self, n: u64) -> (Self, u64) {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_rem_small(n)
        } else {
            self.checked_div_rem_small(n).expect("attempt to divide with overflow")
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    /// This panics if the divisor is 0.
    #[inline(always)]
    pub fn wrapping_div_rem_small(self, n: u64) -> (Self, u64) {
        // SAFETY: Safe since these are plain old data.
        unsafe {
            let x: [u64; 4] = mem::transmute(self.to_le_bytes());
            let (div, rem) = math::div_rem_small(&x, n);
            let div = u256::from_le_bytes(mem::transmute::<[u64; 4], [u8; 32]>(div));
            (div, rem)
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_rem_small(self, n: u64) -> Option<(Self, u64)> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_rem_small(n))
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_rem_small(self, n: u64) -> ((Self, u64), bool) {
        if n == 0 {
            ((Self::MAX, 0), true)
        } else {
            (self.wrapping_div_rem_small(n), false)
        }
    }

    /// Div the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn div_small(self, n: u64) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.div_rem_small(n).0
        } else {
            self.checked_div_small(n).expect("attempt to divide by zero")
        }
    }

    /// Div the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_div_small(self, n: u64) -> Self {
        self.wrapping_div_rem_small(n).0
    }

    /// Div the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_small(self, n: u64) -> (Self, bool) {
        let (divrem, overflow) = self.overflowing_div_rem_small(n);
        (divrem.0, overflow)
    }

    /// Div the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_small(self, n: u64) -> Option<Self> {
        Some(self.checked_div_rem_small(n)?.0)
    }

    /// Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn rem_small(self, n: u64) -> u64 {
        if cfg!(not(have_overflow_checks)) {
            self.div_rem_small(n).1
        } else {
            self.checked_rem_small(n).expect("attempt to divide by zero")
        }
    }

    /// Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_rem_small(self, n: u64) -> u64 {
        self.wrapping_div_rem_small(n).1
    }

    /// Div the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_rem_small(self, n: u64) -> (u64, bool) {
        let (divrem, overflow) = self.overflowing_div_rem_small(n);
        (divrem.1, overflow)
    }

    /// Div the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_rem_small(self, n: u64) -> Option<u64> {
        Some(self.checked_div_rem_small(n)?.1)
    }
}

impl Add for u256 {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_add(rhs)
        } else {
            self.checked_add(rhs).expect("attempt to add with overflow")
        }
    }
}

op_impl!(u256, Add, AddAssign, add, add_assign);

impl fmt::Binary for u256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: This works for binary, since the value as always divisible.
        if f.alternate() {
            write!(f, "{:#b}", self.hi)?;
        } else {
            write!(f, "{:b}", self.hi)?;
        }
        write!(f, "{:b}", self.lo)
    }
}

impl BitAnd for u256 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        bitand(self, rhs)
    }
}

op_impl!(u256, BitAnd, BitAndAssign, bitand, bitand_assign);

impl BitOr for u256 {
    type Output = u256;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        bitor(self, rhs)
    }
}

op_impl!(u256, BitOr, BitOrAssign, bitor, bitor_assign);

impl BitXor for u256 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self::Output {
        bitxor(self, rhs)
    }
}

op_impl!(u256, BitXor, BitXorAssign, bitxor, bitxor_assign);

impl fmt::Debug for u256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for u256 {
    #[inline(always)]
    #[allow(clippy::bind_instead_of_map)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.hi == 0 {
            return fmt::Display::fmt(&self.hi, f);
        }

        let mut buffer = [0u8; 78];
        let formatted = to_string(*self, &mut buffer).or_else(|_| Err(fmt::Error))?;
        write!(f, "{}", formatted)
    }
}

impl Div for u256 {
    type Output = Self;

    #[inline(always)]
    fn div(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div(rhs)
        } else {
            self.checked_div(rhs).expect("attempt to divide by zero")
        }
    }
}

op_impl!(u256, Div, DivAssign, div, div_assign);

impl From<bool> for u256 {
    #[inline(always)]
    fn from(small: bool) -> Self {
        Self::new(small as u128, 0)
    }
}

impl From<char> for u256 {
    #[inline(always)]
    fn from(c: char) -> Self {
        Self::new(c as u128, 0)
    }
}

from_impl!(u256, u8, from_u8);
from_impl!(u256, u16, from_u16);
from_impl!(u256, u32, from_u32);
from_impl!(u256, u64, from_u64);
from_impl!(u256, u128, from_u128);

impl FromStr for u256 {
    type Err = ParseIntError;

    /// Parses a string s to return a value of this type.
    ///
    /// This is not optimized, since all optimization is done in
    /// the lexical implementation.
    #[inline(always)]
    fn from_str(src: &str) -> Result<u256, ParseIntError> {
        // up to 39 digits can be stored in a `u128`, so less is always valid
        // meanwhile, 78 is good for all 256-bit integers. 32-bit architectures
        // on average have poor support for 128-bit operations so we try to use `u64`.
        if (cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32"))
            && src.len() < 20
        {
            Ok(u256::from_u64(u64::from_str(src)?))
        } else if src.len() < 39 {
            Ok(u256::from_u128(u128::from_str(src)?))
        } else {
            u256::from_str_radix(src, 10)
        }
    }
}

impl fmt::LowerExp for u256 {
    #[inline(always)]
    #[allow(clippy::bind_instead_of_map)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.hi == 0 {
            return fmt::LowerExp::fmt(&self.hi, f);
        }

        let mut buffer = [0u8; 78];
        let buffer = to_bytes(*self, &mut buffer);
        let first = buffer[0] as char;
        let formatted = str::from_utf8(&buffer[1..]).or_else(|_| Err(fmt::Error))?;
        write!(f, "{}.{}e{}", first, formatted, buffer.len() - 1)
    }
}

impl fmt::LowerHex for u256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: This works for hex, since the value as always divisible.
        if f.alternate() {
            write!(f, "{:#x}", self.hi)?;
        } else {
            write!(f, "{:x}", self.hi)?;
        }
        write!(f, "{:x}", self.lo)
    }
}

impl Mul for u256 {
    type Output = u256;

    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul(rhs)
        } else {
            self.checked_mul(rhs).expect("attempt to multiply with overflow")
        }
    }
}

op_impl!(u256, Mul, MulAssign, mul, mul_assign);

impl Not for u256 {
    type Output = u256;

    #[inline(always)]
    fn not(self) -> Self::Output {
        not(self)
    }
}

ref_impl!(u256, Not, not);

impl fmt::Octal for u256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: This is **NOT** divisible by 8, so `log(128, 8)` is not integral.
        // So, we can break it into pairs of u64.
        let hi1 = (self.hi >> 64) as u64;
        let hi0 = self.hi as u64;
        let lo1 = (self.lo >> 64) as u64;
        let lo0 = self.lo as u64;

        let alternate = f.alternate();
        let mut write = |x: u64, alt: bool| {
            if alt {
                write!(f, "{:#o}", x)
            } else {
                write!(f, "{:o}", x)
            }
        };
        if hi1 != 0 {
            write(hi1, alternate)?;
            write(hi0, false)?;
            write(lo1, false)?;
            write(lo0, false)
        } else if hi0 != 0 {
            write(hi0, alternate)?;
            write(lo1, false)?;
            write(lo0, false)
        } else if lo1 != 0 {
            write(lo1, alternate)?;
            write(lo0, false)
        } else {
            // NOTE: Always write at least a 0
            write(lo0, alternate)
        }
    }
}

impl Ord for u256 {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        cmp(*self, *other)
    }
}

impl PartialOrd for u256 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }

    #[inline(always)]
    fn lt(&self, other: &Self) -> bool {
        lt(*self, *other)
    }

    #[inline(always)]
    fn le(&self, other: &Self) -> bool {
        le(*self, *other)
    }

    #[inline(always)]
    fn gt(&self, other: &Self) -> bool {
        gt(*self, *other)
    }

    #[inline(always)]
    fn ge(&self, other: &Self) -> bool {
        ge(*self, *other)
    }
}

impl Rem for u256 {
    type Output = u256;

    #[inline(always)]
    fn rem(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_rem(rhs)
        } else {
            self.checked_rem(rhs)
                .expect("attempt to calculate the remainder with a divisor of zero")
        }
    }
}

op_impl!(u256, Rem, RemAssign, rem, rem_assign);

macro_rules! shift_const_impl {
    (@shl $value:ident, $shift:ident) => {{
        let (lo, hi) = math::shl_u128($value.lo, $value.hi, $shift as u32);
        Self::new(lo, hi)
    }};

    (@shr $value:ident, $shift:ident) => {{
        let (lo, hi) = math::shr_u128($value.lo, $value.hi, $shift as u32);
        Self::new(lo, hi)
    }};

    (@nomod $t:ty, $shl:ident, $shr:ident) => (
        /// Const evaluation of shl.
        #[inline(always)]
        pub const fn $shl(self, other: $t) -> Self {
            let other = other as u32;
            shift_const_impl!(@shl self, other)
        }

        /// Const evaluation of shr.
        pub const fn $shr(self, other: $t) -> Self {
            let other = other as u32;
            shift_const_impl!(@shr self, other)
        }
    );

    ($t:ty, $shl:ident, $shr:ident) => (
        /// Const evaluation of shl.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        #[inline(always)]
        pub const fn $shl(self, other: $t) -> Self {
            debug_assert!(other < 256, "attempt to shift left with overflow");
            let other = other as u32;
            shift_const_impl!(@shl self, other)
        }

        /// Const evaluation of shr.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        pub const fn $shr(self, other: $t) -> Self {
            debug_assert!(other < 256, "attempt to shift right with overflow");
            let other = other as u32;
            shift_const_impl!(@shr self, other)
        }
    );

    (@256 $t:ty, $shl:ident, $shr:ident) => (
        /// Const evaluation of shl.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        #[inline(always)]
        pub const fn $shl(self, other: $t) -> Self {
            let max = Self::from_u16(256);
            let other = other.as_u256();
            debug_assert!(lt(other, max), "attempt to shift left with overflow");
            let shift = (other.lo & (u32::MAX as u128)) as u32;
            shift_const_impl!(@shl self, shift)
        }

        /// Const evaluation of shr.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        pub const fn $shr(self, other: $t) -> Self {
            let max = Self::from_u16(256);
            let other = other.as_u256();
            debug_assert!(lt(other, max), "attempt to shift right with overflow");
            let shift = other.lo & (u32::MAX as u128);
            shift_const_impl!(@shr self, shift)
        }
    );
}

// Const implementations for Shl
impl u256 {
    shift_const_impl!(@nomod i8, shl_i8, shr_i8);
    shift_const_impl!(i16, shl_i16, shr_i16);
    shift_const_impl!(i32, shl_i32, shr_i32);
    shift_const_impl!(i64, shl_i64, shr_i64);
    shift_const_impl!(i128, shl_i128, shr_i128);
    shift_const_impl!(@256 i256, shl_i256, shr_i256);
    shift_const_impl!(isize, shl_isize, shr_isize);
    shift_const_impl!(@nomod u8, shl_u8, shr_u8);
    shift_const_impl!(u16, shl_u16, shr_u16);
    shift_const_impl!(u32, shl_u32, shr_u32);
    shift_const_impl!(u64, shl_u64, shr_u64);
    shift_const_impl!(u128, shl_u128, shr_u128);
    shift_const_impl!(@256 u256, shl_u256, shr_u256);
    shift_const_impl!(usize, shl_usize, shr_usize);
}

impl Shl for u256 {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shl(self, other: Self) -> Self::Output {
        let shift = other.lo & (u32::MAX as u128);
        shift_const_impl!(@shl self, shift)
    }
}

ref_impl!(u256, Shl, shl, other: &u256);
ref_t_impl!(u256, Shl, shl);

impl Shr for u256 {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shr(self, other: Self) -> Self::Output {
        let shift = other.lo & (u32::MAX as u128);
        shift_const_impl!(@shr self, shift)
    }
}

ref_impl!(u256, Shr, shr, other: &u256);
ref_t_impl!(u256, Shr, shr);

macro_rules! shift_impl {
    (@mod $($t:ty)*) => ($(
        impl Shl<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                let shift = other % 256;
                shift_const_impl!(@shl self, shift)
            }
        }

        impl Shr<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shr(self, other: $t) -> Self::Output {
                let shift = other % 256;
                shift_const_impl!(@shr self, shift)
            }
        }
    )*);

    (@nomod $($t:ty)*) => ($(
        impl Shl<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            fn shl(self, other: $t) -> Self::Output {
                shift_const_impl!(@shl self, other)
            }
        }

        impl Shr<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            fn shr(self, other: $t) -> Self::Output {
                shift_const_impl!(@shr self, other)
            }
        }
    )*);

    (@256 $($t:ty)*) => ($(
        impl Shl<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                let shift = other % i256::from_u16(256);
                let shift = shift.as_u32();
                shift_const_impl!(@shl self, shift)
            }
        }

        impl Shr<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shr(self, other: $t) -> Self::Output {
                let shift = other % i256::from_u16(256);
                let shift = shift.as_u32();
                shift_const_impl!(@shr self, shift)
            }
        }
    )*);

    ($($t:ty)*) => ($(
        impl Shl<&$t> for u256 {
            type Output = <Self as Shl>::Output;

            #[inline(always)]
            fn shl(self, other: &$t) -> Self::Output {
                self.shl(*other)
            }
        }

        impl ShlAssign<$t> for u256 {
            #[inline(always)]
            fn shl_assign(&mut self, other: $t) {
                *self = self.shl(other);
            }
        }

        impl ShlAssign<&$t> for u256 {
            #[inline(always)]
            fn shl_assign(&mut self, other: &$t) {
                *self = self.shl(other);
            }
        }

        impl Shr<&$t> for u256 {
            type Output = <Self as Shr>::Output;

            #[inline(always)]
            fn shr(self, other: &$t) -> Self::Output {
                self.shr(*other)
            }
        }

        impl ShrAssign<$t> for u256 {
            #[inline(always)]
            fn shr_assign(&mut self, other: $t) {
                *self = self.shr(other);
            }
        }

        impl ShrAssign<&$t> for u256 {
            #[inline(always)]
            fn shr_assign(&mut self, other: &$t) {
                *self = self.shr(other);
            }
        }
    )*);
}

shift_impl! { @nomod i8 u8 }
shift_impl! { @mod i16 i32 i64 i128 isize u16 u32 u64 u128 usize }
shift_impl! { @256 i256 }
shift_impl! { i8 i16 i32 i64 i128 i256 isize u8 u16 u32 u64 u128 usize }

impl Sub for u256 {
    type Output = u256;

    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_sub(rhs)
        } else {
            self.checked_sub(rhs).expect("attempt to subtract with overflow")
        }
    }
}

op_impl!(u256, Sub, SubAssign, sub, sub_assign);

macro_rules! try_from_impl {
    ($($t:ty)*) => ($(
        impl TryFrom<$t> for u256 {
            type Error = TryFromIntError;

            #[inline(always)]
            fn try_from(u: $t) -> Result<Self, TryFromIntError> {
                if u >= 0 {
                    Ok(Self::from_u128(u as u128))
                } else {
                    Err(TryFromIntError {})
                }
            }
        }
    )*);
}

try_from_impl! { i8 i16 i32 i64 i128 isize }

impl TryFrom<i256> for u256 {
    type Error = TryFromIntError;

    #[inline(always)]
    fn try_from(u: i256) -> Result<Self, TryFromIntError> {
        if u.hi >= 0 {
            Ok(u.as_u256())
        } else {
            Err(TryFromIntError {})
        }
    }
}

impl fmt::UpperExp for u256 {
    #[inline(always)]
    #[allow(clippy::bind_instead_of_map)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.hi == 0 {
            return fmt::UpperExp::fmt(&self.hi, f);
        }

        let mut buffer: [u8; 78] = [0u8; 78];
        let buffer = to_bytes(*self, &mut buffer);
        let first = buffer[0] as char;
        let formatted = str::from_utf8(&buffer[1..]).or_else(|_| Err(fmt::Error))?;
        write!(f, "{}.{}E{}", first, formatted, buffer.len() - 1)
    }
}

impl fmt::UpperHex for u256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: This works for hex, since the value as always divisible.
        if f.alternate() {
            write!(f, "{:#X}", self.hi)?;
        } else {
            write!(f, "{:X}", self.hi)?;
        }
        write!(f, "{:X}", self.lo)
    }
}

// NOTE: Our algorithm assumes little-endian order, which we might not have.
// So, we transmute to LE order prior to the call.
/// Large division/remainder calculation. This will panic if rhs is 0.
#[inline]
fn div_rem(lhs: u256, rhs: u256) -> (u256, u256) {
    // SAFETY: Safe since these are plain old data.
    unsafe {
        let x: [u64; 4] = mem::transmute::<[u8; 32], [u64; 4]>(lhs.to_le_bytes());
        let y: [u64; 4] = mem::transmute::<[u8; 32], [u64; 4]>(rhs.to_le_bytes());

        let (div, rem) = math::div_rem_big(&x, &y);
        let div = u256::from_le_bytes(mem::transmute::<[u64; 4], [u8; 32]>(div));
        let rem = u256::from_le_bytes(mem::transmute::<[u64; 4], [u8; 32]>(rem));

        (div, rem)
    }
}

/// Const implementation of `BitAnd` for internal algorithm use.
#[inline(always)]
const fn bitand(lhs: u256, rhs: u256) -> u256 {
    u256::new(lhs.lo & rhs.lo, lhs.hi & rhs.hi)
}

/// Const implementation of `BitOr` for internal algorithm use.
#[inline(always)]
const fn bitor(lhs: u256, rhs: u256) -> u256 {
    u256::new(lhs.lo | rhs.lo, lhs.hi | rhs.hi)
}

/// Const implementation of `BitXor` for internal algorithm use.
#[inline(always)]
const fn bitxor(lhs: u256, rhs: u256) -> u256 {
    u256::new(lhs.lo ^ rhs.lo, lhs.hi ^ rhs.hi)
}

/// Const implementation of `Not` for internal algorithm use.
#[inline(always)]
const fn not(n: u256) -> u256 {
    u256::new(!n.lo, !n.hi)
}

/// Const implementation of `Eq` for internal algorithm use.
#[inline(always)]
const fn eq(lhs: u256, rhs: u256) -> bool {
    lhs.lo == rhs.lo && lhs.hi == rhs.hi
}

/// Const implementation of `PartialOrd::lt` for internal algorithm use.
#[inline(always)]
pub(crate) const fn lt(lhs: u256, rhs: u256) -> bool {
    lhs.hi < rhs.hi || (lhs.hi == rhs.hi && lhs.lo < rhs.lo)
}

/// Const implementation of `PartialOrd::le` for internal algorithm use.
#[inline(always)]
const fn le(lhs: u256, rhs: u256) -> bool {
    lhs.hi < rhs.hi || (lhs.hi == rhs.hi && lhs.lo <= rhs.lo)
}

/// Const implementation of `PartialOrd::gt` for internal algorithm use.
#[inline(always)]
const fn gt(lhs: u256, rhs: u256) -> bool {
    lhs.hi > rhs.hi || (lhs.hi == rhs.hi && lhs.lo > rhs.lo)
}

/// Const implementation of `PartialOrd::ge` for internal algorithm use.
#[inline(always)]
const fn ge(lhs: u256, rhs: u256) -> bool {
    lhs.hi > rhs.hi || (lhs.hi == rhs.hi && lhs.lo >= rhs.lo)
}

/// Const implementation of `PartialOrd::cmp` for internal algorithm use.
#[inline(always)]
const fn cmp(lhs: u256, rhs: u256) -> Ordering {
    if lhs.hi < rhs.hi {
        Ordering::Less
    } else if lhs.hi > rhs.hi {
        Ordering::Greater
    } else if lhs.lo < rhs.lo {
        Ordering::Less
    } else if lhs.lo > rhs.lo {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

#[inline]
fn to_bytes(mut value: u256, buffer: &mut [u8; 78]) -> &[u8] {
    // We're not optimizing for this at all, since we'll implement
    // it well in the integer writers (max 78 digits).

    // only want to write until
    let mut rem: u64;
    let mut index = buffer.len();
    while value.hi > 0 || value.lo > 10 && index > 1 {
        index -= 1;
        (value, rem) = value.div_rem_small(10);
        buffer[index] = b'0' + rem as u8;
    }
    // always have one trailing digit
    index -= 1;
    buffer[index] = b'0' + value.lo as u8;
    &buffer[index..]
}

#[inline]
fn to_string(value: u256, buffer: &mut [u8; 78]) -> Result<&str, Utf8Error> {
    str::from_utf8(to_bytes(value, buffer))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_test() {
        // NOTE: This is mostly covered elsewhere
        assert_eq!(u256::from_u8(1).wrapping_add(u256::from_u8(1)), u256::from_u8(2));
        assert_eq!(u256::MAX.wrapping_add(u256::MAX), u256::new(u128::MAX - 1, u128::MAX));
    }

    #[test]
    fn display_test() {
        let max = u256::MAX;
        let result = max.to_string();
        assert_eq!(
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            result
        );

        let value = u256::new(0, 1);
        let result = value.to_string();
        assert_eq!("340282366920938463463374607431768211456", result);
    }

    #[test]
    fn lower_exp_test() {
        let max = u256::MAX;
        let result = format!("{:e}", max);
        assert_eq!(
            "1.15792089237316195423570985008687907853269984665640564039457584007913129639935e77",
            result
        );

        let value = u256::new(0, 1);
        let result = format!("{:e}", value);
        assert_eq!("3.40282366920938463463374607431768211456e38", result);
    }

    #[test]
    fn upper_exp_test() {
        let max = u256::MAX;
        let result = format!("{:E}", max);
        assert_eq!(
            "1.15792089237316195423570985008687907853269984665640564039457584007913129639935E77",
            result
        );

        let value = u256::new(0, 1);
        let result = format!("{:E}", value);
        assert_eq!("3.40282366920938463463374607431768211456E38", result);
    }
}
