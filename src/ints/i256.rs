//! An signed 256-bit integer type.
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

use core::cmp::Ordering;
use core::fmt;
use core::ops::*;
use core::str::FromStr;

use super::macros::from_str_radix_impl;
use crate::error::{ParseIntError, TryFromIntError};
use crate::ints::u256::lt as u256_lt;
use crate::math::{self, ILimb, IWide, ULimb, UWide, LIMBS};
use crate::numtypes::*;
use crate::u256;

// FIXME: Add support for [Saturating][core::num::Saturating] and
// [Wrapping][core::num::Wrapping] when we drop support for <1.74.0.

/// The 256-bit signed integer type.
///
/// The high and low words depend on the target endianness.
/// Conversion to and from big endian should be done via
/// [`to_le_bytes`] and [`to_be_bytes`]. or using
/// [`high`] and [`low`].
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
/// [`high`]: i256::high
/// [`low`]: i256::low
/// [`alternate`]: fmt::Formatter::alternate
/// [`Binary`]: fmt::Binary
/// [`128-bit`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
pub struct i256 {
    // NOTE: This is currently FFI-safe (if we did repr(C)) but we
    // intentionally make  no guarantees so we're free to re-arrange
    // the layout.
    limbs: [ULimb; LIMBS],
}

impl i256 {
    /// The smallest value that can be represented by this integer type.
    ///
    /// See [`i128::MIN`].
    pub const MIN: Self = Self::new(0, i128::MIN);

    /// The largest value that can be represented by this integer type
    /// (2<sup>256</sup> - 1).
    ///
    /// See [`i128::MAX`].
    pub const MAX: Self = Self::new(u128::MAX, i128::MAX);

    /// The size of this integer type in bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use i256::i256;
    /// assert_eq!(i256::BITS, 256);
    /// ```
    ///
    /// See [`i128::BITS`].
    pub const BITS: u32 = 256;

    /// Returns the number of ones in the binary representation of `self`.
    ///
    /// See [`i128::count_ones`].
    #[inline(always)]
    pub const fn count_ones(self) -> u32 {
        self.high().count_ones() + self.low().count_ones()
    }

    /// Returns the number of zeros in the binary representation of `self`.
    ///
    /// See [`i128::count_zeros`].
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
    /// # use i256::i256;
    /// let n = i256::MAX >> 2i32;
    /// assert_eq!(n.leading_zeros(), 3);
    ///
    /// let min = i256::MIN;
    /// assert_eq!(min.leading_zeros(), 0);
    ///
    /// let zero = i256::from_u8(0);
    /// assert_eq!(zero.leading_zeros(), 256);
    ///
    /// let max = i256::MAX;
    /// assert_eq!(max.leading_zeros(), 1);
    /// ```
    ///
    /// See [`i128::leading_zeros`].
    #[inline]
    pub const fn leading_zeros(self) -> u32 {
        let mut leading = (self.high() as u128).leading_zeros();
        if leading == u128::BITS {
            leading += self.low().leading_zeros();
        }
        leading
    }

    /// Returns the number of trailing zeros in the binary representation of
    /// `self`.
    ///
    /// See [`i128::trailing_zeros`].
    #[inline]
    pub const fn trailing_zeros(self) -> u32 {
        let mut trailing = self.low().trailing_zeros();
        if trailing == u128::BITS {
            trailing += self.high().trailing_zeros();
        }
        trailing
    }

    /// Returns the number of leading ones in the binary representation of
    /// `self`.
    ///
    /// See [`i128::leading_ones`].
    #[inline(always)]
    pub const fn leading_ones(self) -> u32 {
        not(self).leading_zeros()
    }

    /// Returns the number of trailing ones in the binary representation of
    /// `self`.
    ///
    /// See [`i128::trailing_ones`].
    #[inline(always)]
    pub const fn trailing_ones(self) -> u32 {
        not(self).trailing_zeros()
    }

    /// Shifts the bits to the left by a specified amount, `n`,
    /// wrapping the truncated bits to the end of the resulting integer.
    ///
    /// Please note this isn't the same operation as the `<<` shifting operator!
    ///
    /// See [`i128::rotate_left`].
    #[inline(always)]
    pub const fn rotate_left(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_left_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Shifts the bits to the right by a specified amount, `n`,
    /// wrapping the truncated bits to the beginning of the resulting
    /// integer.
    ///
    /// Please note this isn't the same operation as the `>>` shifting operator!
    ///
    /// See [`i128::rotate_right`].
    #[inline(always)]
    pub const fn rotate_right(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_right_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Reverses the byte order of the integer.
    ///
    /// See [`i128::swap_bytes`].
    #[inline(always)]
    pub const fn swap_bytes(self) -> Self {
        let (lo, hi) = math::swap_bytes_i128(self.low(), self.high());
        Self::new(lo, hi)
    }

    /// Reverses the order of bits in the integer. The least significant
    /// bit becomes the most significant bit, second least-significant bit
    /// becomes second most-significant bit, etc.
    ///
    /// See [`i128::reverse_bits`].
    #[inline(always)]
    pub const fn reverse_bits(self) -> Self {
        let (lo, hi) = math::reverse_bits_i128(self.low(), self.high());
        Self::new(lo, hi)
    }

    /// Converts an integer from big endian to the target's endianness.
    ///
    /// On big endian this is a no-op. On little endian the bytes are
    /// swapped.
    ///
    /// See [`i128::from_be`].
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
    ///
    /// See [`i128::from_le`].
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
    ///
    /// See [`i128::to_be`].
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
    ///
    /// See [`i128::to_le`].
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
    ///
    /// See [`i128::checked_add`].
    #[inline(always)]
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked addition with an unsigned integer. Computes `self + rhs`,
    /// returning `None` if overflow occurred.
    ///
    /// See [`i128::checked_add_unsigned`].
    #[inline(always)]
    pub const fn checked_add_unsigned(self, rhs: u256) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add_unsigned(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning `None`
    /// if overflow occurred.
    ///
    /// See [`i128::checked_sub`].
    #[inline(always)]
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked subtraction with an unsigned integer. Computes `self - rhs`,
    /// returning `None` if overflow occurred.
    ///
    /// See [`i128::checked_sub_unsigned`].
    #[inline(always)]
    pub const fn checked_sub_unsigned(self, rhs: u256) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub_unsigned(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning `None`
    /// if overflow occurred.
    ///
    /// See [`i128::checked_mul`].
    #[inline(always)]
    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    #[inline(always)]
    const fn is_div_none(self, rhs: Self) -> bool {
        eq(rhs, Self::from_u8(0)) || (eq(self, Self::MIN) && eq(rhs, Self::from_i8(-1)))
    }

    /// Checked integer division. Computes `self / rhs`, returning `None` if
    /// `rhs == 0` or the division results in overflow.
    ///
    /// See [`i128::checked_div`].
    #[inline(always)]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        if self.is_div_none(rhs) {
            None
        } else {
            Some(self.wrapping_div(rhs))
        }
    }

    /// Checked Euclidean division. Computes `self.div_euclid(rhs)`,
    /// returning `None` if `rhs == 0` or the division results in overflow.
    ///
    /// See [`i128::checked_div_euclid`].
    #[inline(always)]
    pub fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
        if self.is_div_none(rhs) {
            None
        } else {
            Some(self.wrapping_div_euclid(rhs))
        }
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None` if
    /// `rhs == 0` or the division results in overflow.
    ///
    /// See [`i128::checked_rem`].
    #[inline(always)]
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        if self.is_div_none(rhs) {
            None
        } else {
            Some(self.wrapping_rem(rhs))
        }
    }

    /// Checked Euclidean remainder. Computes `self.rem_euclid(rhs)`, returning
    /// `None` if `rhs == 0` or the division results in overflow.
    ///
    /// See [`i128::checked_rem_euclid`].
    #[inline(always)]
    pub fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
        if self.is_div_none(rhs) {
            None
        } else {
            Some(self.wrapping_rem_euclid(rhs))
        }
    }

    /// Checked negation. Computes `-self`, returning `None` if `self == MIN`.
    ///
    /// See [`i128::checked_neg`].
    #[inline(always)]
    pub const fn checked_neg(self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_neg();
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked shift left. Computes `self << rhs`, returning `None` if `rhs` is
    /// larger than or equal to the number of bits in `self`.
    ///
    /// See [`i128::checked_shl`].
    #[inline(always)]
    pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
        // Not using overflowing_shl as that's a wrapping shift
        if rhs < Self::BITS {
            Some(self.wrapping_shl(rhs))
        } else {
            None
        }
    }

    /// Checked shift right. Computes `self >> rhs`, returning `None` if `rhs`
    /// is larger than or equal to the number of bits in `self`.
    ///
    /// See [`i128::checked_shr`].
    #[inline(always)]
    pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
        // Not using overflowing_shr as that's a wrapping shift
        if rhs < Self::BITS {
            Some(self.wrapping_shr(rhs))
        } else {
            None
        }
    }

    /// Checked absolute value. Computes `self.abs()`, returning `None` if
    /// `self == MIN`.
    ///
    /// See [`i128::checked_abs`].
    #[inline(always)]
    pub const fn checked_abs(self) -> Option<Self> {
        match self.overflowing_abs() {
            (value, false) => Some(value),
            _ => None,
        }
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if
    /// overflow occurred.
    ///
    /// See [`i128::checked_pow`].
    #[inline]
    pub const fn checked_pow(self, exp: u32) -> Option<Self> {
        match self.overflowing_pow(exp) {
            (value, false) => Some(value),
            _ => None,
        }
    }

    // FIXME: Stabilize when our MSRV goes to `1.84.0+`.
    // /// Returns the square root of the number, rounded down.
    // ///
    // /// Returns `None` if `self` is negative.
    // #[inline]
    // pub const fn checked_isqrt(self) -> Option<Self> {
    //     todo!();
    // }

    /// Saturating integer addition. Computes `self + rhs`, saturating at the
    /// numeric bounds instead of overflowing.
    ///
    /// See [`i128::saturating_add`].
    #[inline(always)]
    pub const fn saturating_add(self, rhs: Self) -> Self {
        match self.checked_add(rhs) {
            Some(value) => value,
            None if self.is_negative() => Self::MIN,
            None => Self::MAX,
        }
    }

    /// Saturating addition with an unsigned integer. Computes `self + rhs`,
    /// saturating at the numeric bounds instead of overflowing.
    ///
    /// See [`i128::saturating_add_unsigned`].
    #[inline(always)]
    pub const fn saturating_add_unsigned(self, rhs: u256) -> Self {
        // Overflow can only happen at the upper bound
        // We cannot use `unwrap_or` here because it is not `const`
        match self.checked_add_unsigned(rhs) {
            Some(x) => x,
            None => Self::MAX,
        }
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the
    /// numeric bounds instead of overflowing.
    ///
    /// See [`i128::saturating_sub`].
    #[inline(always)]
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        match self.checked_sub(rhs) {
            Some(value) => value,
            None if self.is_negative() => Self::MIN,
            None => Self::MAX,
        }
    }

    /// Saturating subtraction with an unsigned integer. Computes `self - rhs`,
    /// saturating at the numeric bounds instead of overflowing.
    ///
    /// See [`i128::saturating_sub_unsigned`].
    #[inline(always)]
    pub const fn saturating_sub_unsigned(self, rhs: u256) -> Self {
        // Overflow can only happen at the lower bound
        // We cannot use `unwrap_or` here because it is not `const`
        match self.checked_sub_unsigned(rhs) {
            Some(x) => x,
            None => Self::MIN,
        }
    }

    /// Saturating integer negation. Computes `-self`, returning `MAX` if `self
    /// == MIN` instead of overflowing.
    ///
    /// See [`i128::saturating_neg`].
    #[inline(always)]
    pub const fn saturating_neg(self) -> Self {
        Self::from_u8(0).saturating_sub(self)
    }

    /// Saturating absolute value. Computes `self.abs()`, returning `MAX` if
    /// `self == MIN` instead of overflowing.
    ///
    /// See [`i128::saturating_abs`].
    #[inline(always)]
    pub const fn saturating_abs(self) -> Self {
        match self.checked_abs() {
            Some(value) => value,
            None => Self::MAX,
        }
    }

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at
    /// the numeric bounds instead of overflowing.
    ///
    /// See [`i128::saturating_mul`].
    #[inline]
    pub const fn saturating_mul(self, rhs: Self) -> Self {
        match self.checked_mul(rhs) {
            Some(x) => x,
            None => {
                if self.is_negative() == rhs.is_negative() {
                    Self::MAX
                } else {
                    Self::MIN
                }
            },
        }
    }

    /// Saturating integer division. Computes `self / rhs`, saturating at the
    /// numeric bounds instead of overflowing.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`i128::saturating_div`].
    #[inline(always)]
    pub fn saturating_div(self, rhs: Self) -> Self {
        match self.overflowing_div(rhs) {
            (result, false) => result,
            (_result, true) => Self::MAX, // MIN / -1 is the only possible saturating overflow
        }
    }

    /// Saturating integer exponentiation. Computes `self.pow(exp)`,
    /// saturating at the numeric bounds instead of overflowing.
    ///
    /// See [`i128::saturating_pow`].
    #[inline]
    pub const fn saturating_pow(self, exp: u32) -> Self {
        match self.checked_pow(exp) {
            Some(x) => x,
            None if lt(self, Self::from_u8(0)) && exp % 2 == 1 => Self::MIN,
            None => Self::MAX,
        }
    }

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at
    /// the boundary of the type.
    ///
    /// See [`i128::wrapping_add`].
    #[inline(always)]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_add_i128(self.low(), self.high(), rhs.low(), rhs.high());
        i256::new(lo, hi)
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around
    /// at the boundary of the type.
    ///
    /// See [`i128::wrapping_sub`].
    #[inline(always)]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_sub_i128(self.low(), self.high(), rhs.low(), rhs.high());
        i256::new(lo, hi)
    }

    /// Wrapping (modular) subtraction with an unsigned integer. Computes
    /// `self - rhs`, wrapping around at the boundary of the type.
    ///
    /// See [`i128::wrapping_sub_unsigned`].
    #[inline(always)]
    pub const fn wrapping_sub_unsigned(self, rhs: u256) -> Self {
        self.wrapping_sub(Self::from_u256(rhs))
    }

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping
    /// around at the boundary of the type.
    ///
    /// See [`i128::wrapping_mul`].
    #[inline(always)]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_mul_i128(self.low(), self.high(), rhs.low(), rhs.high());
        i256::new(lo, hi)
    }

    /// Wrapping (modular) division. Computes `self / rhs`, wrapping around at
    /// the boundary of the type.
    ///
    /// The only case where such wrapping can occur is when one divides `MIN /
    /// -1` on a signed type (where `MIN` is the negative minimal value for
    /// the type); this is equivalent to `-MIN`, a positive value
    /// that is too large to represent in the type. In such a case, this
    /// function returns `MIN` itself.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`i128::wrapping_div`].
    #[inline(always)]
    pub fn wrapping_div(self, rhs: Self) -> Self {
        self.wrapping_div_rem(rhs).0
    }

    /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`,
    /// wrapping around at the boundary of the type.
    ///
    /// Wrapping will only occur in `MIN / -1` on a signed type (where `MIN` is
    /// the negative minimal value for the type). This is equivalent to
    /// `-MIN`, a positive value that is too large to represent in the type.
    /// In this case, this method returns `MIN` itself.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`i128::wrapping_div_euclid`].
    #[inline]
    pub fn wrapping_div_euclid(self, rhs: Self) -> Self {
        let mut q = self.wrapping_div(rhs);
        if lt(self.wrapping_rem(rhs), Self::from_u8(0)) {
            if gt(rhs, Self::from_u8(0)) {
                q = q.wrapping_sub(Self::from_u8(1));
            } else {
                q = q.wrapping_add(Self::from_u8(1));
            }
        }
        q
    }

    /// Wrapping (modular) remainder. Computes `self % rhs`, wrapping around at
    /// the boundary of the type.
    ///
    /// Such wrap-around never actually occurs mathematically; implementation
    /// artifacts make `x % y` invalid for `MIN / -1` on a signed type
    /// (where `MIN` is the negative minimal value). In such a case,
    /// this function returns `0`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`i128::wrapping_rem`].
    #[inline(always)]
    pub fn wrapping_rem(self, rhs: Self) -> Self {
        self.wrapping_div_rem(rhs).1
    }

    /// Wrapping Euclidean remainder. Computes `self.rem_euclid(rhs)`, wrapping
    /// around at the boundary of the type.
    ///
    /// Wrapping will only occur in `MIN % -1` on a signed type (where `MIN` is
    /// the negative minimal value for the type). In this case, this method
    /// returns 0.
    ///
    /// See [`i128::wrapping_rem_euclid`].
    #[inline]
    pub fn wrapping_rem_euclid(self, rhs: Self) -> Self {
        let r = self.wrapping_rem(rhs);
        if lt(r, Self::from_u8(0)) {
            // Semantically equivalent to `if rhs < 0 { r - rhs } else { r + rhs }`.
            // If `rhs` is not `Self::MIN`, then `r + abs(rhs)` will not overflow
            // and is clearly equivalent, because `r` is negative.
            // Otherwise, `rhs` is `Self::MIN`, then we have
            // `r.wrapping_add(Self::MIN.wrapping_abs())`, which evaluates
            // to `r.wrapping_add(Self::MIN)`, which is equivalent to
            // `r - Self::MIN`, which is what we wanted (and will not overflow
            // for negative `r`).
            r.wrapping_add(rhs.wrapping_abs())
        } else {
            r
        }
    }

    /// Wrapping (modular) negation. Computes `-self`, wrapping around at the
    /// boundary of the type.
    ///
    /// The only case where such wrapping can occur is when one negates `MIN` on
    /// a signed type (where `MIN` is the negative minimal value for the
    /// type); this is a positive value that is too large to represent
    /// in the type. In such a case, this function returns `MIN` itself.
    ///
    /// See [`i128::wrapping_neg`].
    #[inline(always)]
    pub const fn wrapping_neg(self) -> Self {
        // NOTE: This is identical to `add(not(x), 1i256)`
        let twos_neg = not(self).wrapping_add(i256::from_u8(1));
        debug_assert!(eq(i256::from_u8(0).wrapping_sub(self), twos_neg));
        i256::from_u8(0).wrapping_sub(self)
    }

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`, where `mask`
    /// removes any high-order bits of `rhs` that would cause the shift to
    /// exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-left; the RHS of a wrapping
    /// shift-left is restricted to the range of the type, rather than the
    /// bits shifted out of the LHS being returned to the other end.
    /// The primitive integer types all implement a
    /// [`rotate_left`](Self::rotate_left) function, which may be what you
    /// want instead.
    ///
    /// See [`i128::wrapping_shl`].
    #[inline(always)]
    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        let (lo, hi) = math::shl_i128(self.low(), self.high(), rhs % 256);
        Self::new(lo, hi)
    }

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`, where `mask`
    /// removes any high-order bits of `rhs` that would cause the shift to
    /// exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-right; the RHS of a
    /// wrapping shift-right is restricted to the range of the type, rather
    /// than the bits shifted out of the LHS being returned to the other
    /// end. The primitive integer types all implement a
    /// [`rotate_right`](Self::rotate_right) function, which may be what you
    /// want instead.
    ///
    /// See [`i128::wrapping_shr`].
    #[inline(always)]
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        let (lo, hi) = math::shr_i128(self.low(), self.high(), rhs % 256);
        Self::new(lo, hi)
    }

    /// Wrapping (modular) absolute value. Computes `self.abs()`, wrapping
    /// around at the boundary of the type.
    ///
    /// The only case where such wrapping can occur is when one takes the
    /// absolute value of the negative minimal value for the type; this is a
    /// positive value that is too large to represent in the type. In such a
    /// case, this function returns `MIN` itself.
    ///
    /// See [`i128::wrapping_abs`].
    #[inline(always)]
    pub const fn wrapping_abs(self) -> Self {
        self.overflowing_abs().0
    }

    /// Computes the absolute value of `self` without any wrapping
    /// or panicking.
    ///
    /// See [`i128::unsigned_abs`].
    #[inline(always)]
    pub const fn unsigned_abs(self) -> u256 {
        self.wrapping_abs().as_u256()
    }

    /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`,
    /// wrapping around at the boundary of the type.
    ///
    /// See [`i128::wrapping_pow`].
    #[inline]
    pub const fn wrapping_pow(self, exp: u32) -> Self {
        // NOTE: We already implement `pow` as a wrapping function.
        self.pow(exp)
    }

    /// Calculates `self` + `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would have
    /// occurred then the wrapped value is returned.
    ///
    /// See [`i128::overflowing_add`].
    #[inline(always)]
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_add_i128(self.low(), self.high(), rhs.low(), rhs.high());
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates `self` + `rhs` with an unsigned `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// See [`i128::overflowing_add_unsigned`].
    #[inline(always)]
    pub const fn overflowing_add_unsigned(self, rhs: u256) -> (Self, bool) {
        let rhs = rhs.as_i256();
        let (res, overflowed) = self.overflowing_add(rhs);
        (res, overflowed ^ lt(rhs, Self::from_u8(0)))
    }

    /// Calculates `self` - `rhs`.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// See [`i128::overflowing_sub`].
    #[inline(always)]
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_sub_i128(self.low(), self.high(), rhs.low(), rhs.high());
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates `self` - `rhs` with an unsigned `rhs`.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// See [`i128::overflowing_sub_unsigned`].
    #[inline(always)]
    pub const fn overflowing_sub_unsigned(self, rhs: u256) -> (Self, bool) {
        let rhs = rhs.as_i256();
        let (res, overflowed) = self.overflowing_sub(rhs);
        (res, overflowed ^ lt(rhs, Self::from_u8(0)))
    }

    /// Calculates the multiplication of `self` and `rhs`.
    ///
    /// Returns a tuple of the multiplication along with a boolean
    /// indicating whether an arithmetic overflow would occur. If an
    /// overflow would have occurred then the wrapped value is returned.
    ///
    /// See [`i128::overflowing_mul`].
    #[inline(always)]
    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_mul_i128(self.low(), self.high(), rhs.low(), rhs.high());
        (i256::new(lo, hi), overflowed)
    }

    /// Calculates the divisor when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating whether
    /// an arithmetic overflow would occur. If an overflow would occur then
    /// self is returned.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`i128::overflowing_div`].
    #[inline(always)]
    pub fn overflowing_div(self, rhs: Self) -> (Self, bool) {
        if eq(rhs, Self::from_i8(-1)) {
            (self, true)
        } else {
            (self.wrapping_div(rhs), false)
        }
    }

    /// Calculates the quotient of Euclidean division `self.div_euclid(rhs)`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating whether
    /// an arithmetic overflow would occur. If an overflow would occur then
    /// `self` is returned.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`i128::overflowing_div_euclid`].
    #[inline(always)]
    pub fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
        if eq(self, Self::MIN) & eq(rhs, Self::from_i8(-1)) {
            (self, true)
        } else {
            (self.wrapping_div_euclid(rhs), false)
        }
    }

    /// Calculates the remainder when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the remainder after dividing along with a boolean
    /// indicating whether an arithmetic overflow would occur. If an
    /// overflow would occur then 0 is returned.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`i128::overflowing_rem`].
    #[inline(always)]
    pub fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
        if eq(rhs, Self::from_i8(-1)) {
            (Self::from_u8(0), eq(self, Self::MIN))
        } else {
            (self.wrapping_rem(rhs), false)
        }
    }

    /// Overflowing Euclidean remainder. Calculates `self.rem_euclid(rhs)`.
    ///
    /// Returns a tuple of the remainder after dividing along with a boolean
    /// indicating whether an arithmetic overflow would occur. If an
    /// overflow would occur then 0 is returned.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`i128::overflowing_rem_euclid`].
    #[inline(always)]
    pub fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
        if eq(self, Self::from_i8(-1)) {
            (Self::from_u8(0), eq(self, Self::MIN))
        } else {
            (self.wrapping_rem_euclid(rhs), false)
        }
    }

    /// Negates self, overflowing if this is equal to the minimum value.
    ///
    /// Returns a tuple of the negated version of self along with a boolean
    /// indicating whether an overflow happened. If `self` is the minimum
    /// value (e.g., `i32::MIN` for values of type `i32`), then the
    /// minimum value will be returned again and `true` will be returned for an
    /// overflow happening.
    ///
    /// See [`i128::overflowing_neg`].
    #[inline(always)]
    pub const fn overflowing_neg(self) -> (Self, bool) {
        if eq(self, Self::MIN) {
            (Self::MIN, true)
        } else {
            (self.wrapping_neg(), false)
        }
    }

    /// Shifts self left by `rhs` bits.
    ///
    /// Returns a tuple of the shifted version of self along with a boolean
    /// indicating whether the shift value was larger than or equal to the
    /// number of bits. If the shift value is too large, then value is
    /// masked (N-1) where N is the number of bits, and this value is then used
    /// to perform the shift.
    ///
    /// See [`i128::overflowing_shl`].
    #[inline(always)]
    pub const fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
        (self.wrapping_shl(rhs), rhs >= Self::BITS)
    }

    /// Shifts self right by `rhs` bits.
    ///
    /// Returns a tuple of the shifted version of self along with a boolean
    /// indicating whether the shift value was larger than or equal to the
    /// number of bits. If the shift value is too large, then value is
    /// masked (N-1) where N is the number of bits, and this value is then used
    /// to perform the shift.
    ///
    /// See [`i128::overflowing_shr`].
    #[inline(always)]
    pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
        (self.wrapping_shr(rhs), rhs >= Self::BITS)
    }

    /// Computes the absolute value of `self`.
    ///
    /// Returns a tuple of the absolute version of self along with a boolean
    /// indicating whether an overflow happened.
    ///
    /// See [`i128::overflowing_abs`].
    #[inline(always)]
    pub const fn overflowing_abs(self) -> (Self, bool) {
        match self.is_negative() {
            true => self.overflowing_neg(),
            false => (self, false),
        }
    }

    /// Raises self to the power of `exp`, using exponentiation by squaring.
    ///
    /// Returns a tuple of the exponentiation along with a bool indicating
    /// whether an overflow happened.
    ///
    /// See [`i128::overflowing_pow`].
    #[inline]
    pub const fn overflowing_pow(self, mut exp: u32) -> (Self, bool) {
        if exp == 0 {
            return (Self::from_u8(1), false);
        }
        let mut base = self;
        let mut acc = Self::from_u8(1);
        let mut overflown = false;
        let mut r: (Self, bool);

        loop {
            if (exp & 1) == 1 {
                r = acc.overflowing_mul(base);
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
        }
    }

    /// Raises self to the power of `exp`, using exponentiation by squaring.
    ///
    /// See [`i128::pow`].
    #[inline]
    pub const fn pow(self, mut exp: u32) -> Self {
        if exp == 0 {
            return Self::from_u8(1);
        }
        let mut base = self;
        let mut acc = Self::from_u8(1);

        loop {
            if (exp & 1) == 1 {
                acc = acc.wrapping_mul(base);
                if exp == 1 {
                    return acc;
                }
            }
            exp /= 2;
            base = base.wrapping_mul(base);
        }
    }

    // FIXME: Stabilize when our MSRV goes to `1.84.0+`.
    // /// Returns the square root of the number, rounded down.
    // ///
    // /// # Panics
    // ///
    // /// This function will panic if `self` is negative.
    // #[inline]
    // pub const fn isqrt(self) -> Self {
    //     match self.checked_isqrt() {
    //         Some(sqrt) => sqrt,
    //         None => panic!("argument of integer square root cannot be negative"),
    //     }
    // }

    /// Calculates the quotient of Euclidean division of `self` by `rhs`.
    ///
    /// This computes the integer `q` such that `self = q * rhs + r`, with
    /// `r = self.rem_euclid(rhs)` and `0 <= r < abs(rhs)`.
    ///
    /// In other words, the result is `self / rhs` rounded to the integer `q`
    /// such that `self >= q * rhs`.
    /// If `self > 0`, this is equal to rounding towards zero (the default in
    /// Rust); if `self < 0`, this is equal to rounding away from zero
    /// (towards +/- infinity). If `rhs > 0`, this is equal to rounding
    /// towards -infinity; if `rhs < 0`, this is equal to rounding towards
    /// +infinity.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero or if `self` is `Self::MIN`
    /// and `rhs` is -1. This behavior is not affected by the `overflow-checks`
    /// flag.
    ///
    /// See [`i128::div_euclid`].
    #[inline(always)]
    pub fn div_euclid(self, rhs: Self) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_euclid(rhs)
        } else {
            self.checked_div_euclid(rhs).expect("attempt to divide with overflow")
        }
    }

    /// Calculates the least nonnegative remainder of `self (mod rhs)`.
    ///
    /// This is done as if by the Euclidean division algorithm -- given
    /// `r = self.rem_euclid(rhs)`, the result satisfies
    /// `self = rhs * self.div_euclid(rhs) + r` and `0 <= r < abs(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero or if `self` is `Self::MIN`
    /// and `rhs` is -1. This behavior is not affected by the
    /// `overflow-checks` flag.
    ///
    /// See [`i128::rem_euclid`].
    #[inline(always)]
    pub fn rem_euclid(self, rhs: Self) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_rem_euclid(rhs)
        } else {
            self.checked_rem_euclid(rhs).expect("attempt to divide with overflow")
        }
    }

    /// Calculates the quotient of `self` and `rhs`, rounding the result towards
    /// negative infinity.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero or if `self` is `Self::MIN`
    /// and `rhs` is -1. This behavior is not affected by the `overflow-checks`
    /// flag.
    ///
    /// See [`i128::div_floor`].
    #[inline]
    pub fn div_floor(self, rhs: Self) -> Self {
        let (d, r) = self.wrapping_div_rem(rhs);

        // If the remainder is non-zero, we need to subtract one if the
        // signs of self and rhs differ, as this means we rounded upwards
        // instead of downwards. We do this branchlessly by creating a mask
        // which is all-ones iff the signs differ, and 0 otherwise. Then by
        // adding this mask (which corresponds to the signed value -1), we
        // get our correction.
        let correction = bitxor(self, rhs) >> (Self::BITS - 1);
        if !eq(r, Self::from_u8(0)) {
            d.wrapping_add(correction)
        } else {
            d
        }
    }

    /// Calculates the quotient of `self` and `rhs`, rounding the result towards
    /// positive infinity.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero or if `self` is `Self::MIN`
    /// and `rhs` is -1. This behavior is not affected by the `overflow-checks`
    /// flag.
    ///
    /// See [`i128::div_ceil`].
    #[inline]
    pub fn div_ceil(self, rhs: Self) -> Self {
        let (d, r) = self.wrapping_div_rem(rhs);

        // When remainder is non-zero we have a.div_ceil(b) == 1 + a.div_floor(b),
        // so we can re-use the algorithm from div_floor, just adding 1.
        let correction = Self::from_u8(1) + ((self ^ rhs) >> (Self::BITS - 1));
        if !eq(r, Self::from_u8(0)) {
            d.wrapping_add(correction)
        } else {
            d
        }
    }

    /// If `rhs` is positive, calculates the smallest value greater than or
    /// equal to `self` that is a multiple of `rhs`. If `rhs` is negative,
    /// calculates the largest value less than or equal to `self` that is a
    /// multiple of `rhs`.
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
    ///
    /// See [`i128::next_multiple_of`].
    #[inline]
    pub fn next_multiple_of(self, rhs: Self) -> Self {
        if eq(rhs, Self::from_i8(-1)) {
            return self;
        }

        let zero = Self::from_u8(0);
        let r = self.wrapping_rem(rhs);
        let m = if (r > zero && rhs < zero) || (r < zero && rhs > zero) {
            r + rhs
        } else {
            r
        };

        if eq(m, zero) {
            self
        } else {
            self + (rhs - m)
        }
    }

    /// If `rhs` is positive, calculates the smallest value greater than or
    /// equal to `self` that is a multiple of `rhs`. If `rhs` is negative,
    /// calculates the largest value less than or equal to `self` that is a
    /// multiple of `rhs`. Returns `None` if `rhs` is zero or the operation
    /// would result in overflow.
    ///
    /// See [`i128::checked_next_multiple_of`].
    #[inline]
    pub fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
        // This would otherwise fail when calculating `r` when self == T::MIN.
        if eq(rhs, Self::from_i8(-1)) {
            return Some(self);
        }

        let zero = Self::from_u8(0);
        let r = self.checked_rem(rhs)?;
        let m = if (r > zero && rhs < zero) || (r < zero && rhs > zero) {
            // r + rhs cannot overflow because they have opposite signs
            r + rhs
        } else {
            r
        };

        if eq(m, zero) {
            Some(self)
        } else {
            // rhs - m cannot overflow because m has the same sign as rhs
            self.checked_add(rhs - m)
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
    /// This function will panic if `self` is less than or equal to zero,
    /// or if `base` is less than 2.
    ///
    /// See [`i128::ilog`].
    #[inline(always)]
    pub fn ilog(self, base: Self) -> u32 {
        assert!(ge(base, Self::from_u8(2)), "base of integer logarithm must be at least 2");
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
    /// This function will panic if `self` is less than or equal to zero.
    ///
    /// See [`i128::ilog2`].
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
    // /// This function will panic if `self` is less than or equal to zero.
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
    /// Returns `None` if the number is negative or zero, or if the base is not
    /// at least 2.
    ///
    /// This method might not be optimized owing to implementation details;
    /// `checked_ilog2` can produce results more efficiently for base 2, and
    /// `checked_ilog10` can produce results more efficiently for base 10.
    ///
    /// See [`i128::checked_ilog`].
    #[inline]
    pub fn checked_ilog(self, base: Self) -> Option<u32> {
        match le(self, Self::from_u8(0)) || le(base, Self::from_u8(1)) {
            true => None,
            false => Some(self.as_u256().ilog(base.as_u256())),
        }
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// Returns `None` if the number is negative or zero.
    ///
    /// See [`i128::checked_ilog2`].
    #[inline]
    pub const fn checked_ilog2(self) -> Option<u32> {
        match le(self, Self::from_u8(0)) {
            true => None,
            false => Some(Self::BITS - 1 - self.leading_zeros()),
        }
    }

    // FIXME: Stabilize when our MSRV goes to `1.67.0+`.
    // /// Returns the base 10 logarithm of the number, rounded down.
    // ///
    // /// Returns `None` if the number is negative or zero.
    // #[inline]
    // pub fn checked_ilog10(self) -> Option<u32> {
    //     match le(self, Self::from_u8(0)) {
    //         true => None,
    //         false => Some(self.as_u256().ilog10()),
    //     }
    // }

    /// Computes the absolute value of `self`.
    ///
    /// See [`i128::abs`].
    #[inline(always)]
    pub const fn abs(self) -> Self {
        match self.checked_abs() {
            Some(value) => value,
            None => panic!("attempt to negate with overflow"),
        }
    }

    /// Computes the absolute difference between `self` and `other`.
    ///
    /// This function always returns the correct answer without overflow or
    /// panics by returning an unsigned integer.
    ///
    /// See [`i128::abs_diff`].
    #[inline(always)]
    pub const fn abs_diff(self, other: Self) -> u256 {
        if lt(self, other) {
            other.as_u256().wrapping_sub(self.as_u256())
        } else {
            self.as_u256().wrapping_sub(other.as_u256())
        }
    }

    /// Returns a number representing sign of `self`.
    ///
    ///  - `0` if the number is zero
    ///  - `1` if the number is positive
    ///  - `-1` if the number is negative
    ///
    /// See [`i128::signum`].
    #[inline(always)]
    pub const fn signum(self) -> Self {
        match cmp(self, Self::from_u8(0)) {
            Ordering::Less => Self::from_i8(-1),
            Ordering::Equal => Self::from_u8(0),
            Ordering::Greater => Self::from_u8(1),
        }
    }

    /// Returns `true` if `self` is positive and `false` if the number is zero
    /// or negative.
    ///
    /// See [`i128::is_positive`].
    #[inline(always)]
    pub const fn is_positive(self) -> bool {
        // NOTE: Because this is 2's complement, we can optimize like this.
        self.high() > 0 || (self.high() == 0 && self.low() > 0)
    }

    /// Returns `true` if `self` is negative and `false` if the number is zero
    /// or positive.
    ///
    /// See [`i128::is_negative`].
    #[inline(always)]
    pub const fn is_negative(self) -> bool {
        // NOTE: Because this is 2's complement, we can optimize like this.
        self.high() < 0
    }

    /// Returns the memory representation of this integer as a byte array in
    /// big-endian (network) byte order.
    ///
    /// See [`i128::to_be_bytes`].
    #[inline(always)]
    pub const fn to_be_bytes(self) -> [u8; 32] {
        math::from_limbs(self.to_be_limbs())
    }

    /// Returns the memory representation of this integer as a byte array in
    /// little-endian byte order.
    ///
    /// See [`i128::to_le_bytes`].
    #[inline(always)]
    pub const fn to_le_bytes(self) -> [u8; 32] {
        math::from_limbs(self.to_le_limbs())
    }

    /// Returns the memory representation of this as a series of limbs in
    /// big-endian (network) byte order.
    #[inline(always)]
    pub const fn to_be_limbs(self) -> [ULimb; LIMBS] {
        self.to_be().limbs
    }

    /// Returns the memory representation of this as a series of limbs in
    /// little-endian byte order.
    #[inline(always)]
    pub const fn to_le_limbs(self) -> [ULimb; LIMBS] {
        self.to_le().limbs
    }

    /// Returns the memory representation of this as a series of limbs.
    ///
    /// As the target platform's native endianness is used, portable code
    /// should use [`to_be_limbs`] or [`to_le_limbs`], as appropriate,
    /// instead.
    ///
    /// [`to_be_limbs`]: Self::to_be_limbs
    /// [`to_le_limbs`]: Self::to_le_limbs
    #[inline(always)]
    pub const fn to_ne_limbs(self) -> [ULimb; LIMBS] {
        self.limbs
    }

    /// Returns the memory representation of this integer as a byte array in
    /// native byte order.
    ///
    /// As the target platform's native endianness is used, portable code
    /// should use [`to_be_bytes`] or [`to_le_bytes`], as appropriate,
    /// instead.
    ///
    /// See [`i128::to_ne_bytes`].
    ///
    /// [`to_be_bytes`]: Self::to_be_bytes
    /// [`to_le_bytes`]: Self::to_le_bytes
    #[inline(always)]
    pub const fn to_ne_bytes(self) -> [u8; 32] {
        math::from_limbs(self.to_ne_limbs())
    }

    /// Creates a native endian integer value from its representation
    /// as a byte array in big endian.
    ///
    /// See [`i128::from_be_bytes`].
    #[inline(always)]
    pub const fn from_be_bytes(bytes: [u8; 32]) -> Self {
        Self::from_be_limbs(math::to_limbs(bytes))
    }

    /// Creates a native endian integer value from its representation
    /// as a byte array in little endian.
    ///
    /// See [`i128::from_le_bytes`].
    #[inline(always)]
    pub const fn from_le_bytes(bytes: [u8; 32]) -> Self {
        Self::from_le_limbs(math::to_limbs(bytes))
    }

    /// Creates a native endian integer value from its memory representation
    /// as a byte array in native endianness.
    ///
    /// As the target platform's native endianness is used, portable code
    /// likely wants to use [`from_be_bytes`] or [`from_le_bytes`], as
    /// appropriate instead.
    ///
    /// See [`i128::from_ne_bytes`].
    ///
    /// [`from_be_bytes`]: Self::from_be_bytes
    /// [`from_le_bytes`]: Self::from_le_bytes
    #[inline(always)]
    pub const fn from_ne_bytes(bytes: [u8; 32]) -> Self {
        Self::from_ne_limbs(math::to_limbs(bytes))
    }

    /// Creates a native endian integer value from its representation
    /// as limbs in big endian.
    #[inline(always)]
    pub const fn from_be_limbs(limbs: [ULimb; LIMBS]) -> Self {
        if cfg!(target_endian = "big") {
            Self::from_ne_limbs(limbs)
        } else {
            Self::from_ne_limbs(math::swap_limbs(limbs))
        }
    }

    /// Creates a native endian integer value from its representation
    /// as limbs in little endian.
    #[inline(always)]
    pub const fn from_le_limbs(limbs: [ULimb; LIMBS]) -> Self {
        if cfg!(target_endian = "big") {
            Self::from_ne_limbs(math::swap_limbs(limbs))
        } else {
            Self::from_ne_limbs(limbs)
        }
    }

    /// Creates a native endian integer value from its memory representation
    /// as limbs in native endianness.
    ///
    /// As the target platform's native endianness is used, portable code
    /// likely wants to use [`from_be_limbs`] or [`from_le_limbs`], as
    /// appropriate instead.
    ///
    /// [`from_be_limbs`]: Self::from_be_limbs
    /// [`from_le_limbs`]: Self::from_le_limbs
    #[inline(always)]
    pub const fn from_ne_limbs(limbs: [ULimb; LIMBS]) -> Self {
        Self {
            limbs,
        }
    }

    /// Converts a string slice in a given base to an integer.
    ///
    /// The string is expected to be an optional `+` or `-`
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
    ///
    /// See [`i128::from_str_radix`].
    #[inline]
    pub const fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        from_str_radix(src, radix)
    }
}

// NOTE: Validation of the bit patterns for types can be done as:
//
// ```python
// from bitstring import BitArray
//
// def sbin(n, l, be='big'):
//     bits = BitArray(n.to_bytes(l, signed=True, byteorder=be)).bin
//     return '0b' + bits
//
// def ubin(n, l, be='big'):
//     bits = BitArray(n.to_bytes(l, signed=False, byteorder=be)).bin
//     return '0b' + bits
// ```
//
// These are output in big-endian order. Great testing includes
// unique bit patterns, like `ubin(0x123579, 4)`, which has a unique
// bit order (`0b00000000000100100011010101111001`), which we can
// check for truncation to `u16` from `u32`, etc., as well as conversions
// to signed and conversions to `i16` from `i32`. Casting to `u16` leaves
// `0x3579`, as does `i32` to `i16`. Similarly, `-0x123579i32 as i16` is
// then truncated to `-0x3579`.
//
// Meanwhile, `sbin(-0x123579`, 4) == 0b11111111111011011100101010000111`.
//
// **Big:**
// - +0x123579i32: 0b00000000 00010010 00110101 01111001
// - -0x123579i32: 0b11111111 11101101 11001010 10000111
//
// - +0x3579i16:   0b                  00110101 01111001
// - -0x3579i16:   0b                  11001010 10000111
//
// **Little:**
// - +0x123579i32: 0b01111001 00110101 00010010 00000000
// - -0x123579i32: 0b10000111 11001010 11101101 11111111
//
// - +0x3579i16:   0b01111001 00110101
// - -0x3579i16:   0b10000111 11001010
//
// Or, the `!0x123579i32 + 1`, as documented. Since we're doing
// a big-endian representation, it means truncation is just taking the high
// words and going from there.

impl i256 {
    /// Create a new `i256` from the low and high bits.
    #[inline(always)]
    pub const fn new(lo: u128, hi: i128) -> Self {
        if cfg!(target_endian = "big") {
            Self::from_be_bytes(math::to_flat_bytes(hi.to_be_bytes(), lo.to_be_bytes()))
        } else {
            Self::from_le_bytes(math::to_flat_bytes(lo.to_le_bytes(), hi.to_le_bytes()))
        }
    }

    /// Get the high 128 bits of the signed integer.
    #[inline(always)]
    pub const fn high(self) -> i128 {
        if cfg!(target_endian = "big") {
            let (hi, _) = math::from_flat_bytes(self.to_be_bytes());
            i128::from_be_bytes(hi)
        } else {
            let (_, hi) = math::from_flat_bytes(self.to_le_bytes());
            i128::from_le_bytes(hi)
        }
    }

    /// Get the low 128 bits of the signed integer.
    #[inline(always)]
    pub const fn low(self) -> u128 {
        if cfg!(target_endian = "big") {
            let (_, lo) = math::from_flat_bytes(self.to_be_bytes());
            u128::from_be_bytes(lo)
        } else {
            let (lo, _) = math::from_flat_bytes(self.to_le_bytes());
            u128::from_le_bytes(lo)
        }
    }

    /// Get if the integer is even.
    #[inline(always)]
    pub const fn is_even(self) -> bool {
        self.low() % 2 == 0
    }

    /// Get if the integer is off.
    #[inline(always)]
    pub const fn is_off(self) -> bool {
        !self.is_even()
    }

    /// Create the 256-bit signed integer to a `u8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u8(value: u8) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit signed integer from a `u16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u16(value: u16) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit signed integer from a `u32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u32(value: u32) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit signed integer from a `u64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u64(value: u64) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit signed integer from a `u128`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u128(value: u128) -> Self {
        let (lo, hi) = math::as_uwide_i128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit signed integer from an `u256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u256(value: u256) -> Self {
        value.as_i256()
    }

    /// Create the 256-bit signed integer from an unsigned limb, as if by an
    /// `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn from_ulimb(value: ULimb) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit signed integer from an unsigned wide type, as if by
    /// an `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn from_uwide(value: UWide) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit signed integer to an `i8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_i8(value: i8) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit signed integer from an `i16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_i16(value: i16) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit signed integer from an `i32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_i32(value: i32) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit signed integer from an `i64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_i64(value: i64) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit signed integer from an `i128`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_i128(value: i128) -> Self {
        let (lo, hi) = math::as_iwide_i128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit signed integer from a signed limb, as if by an `as`
    /// cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn from_ilimb(value: ILimb) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit signed integer from a signed wide type, as if by an
    /// `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn from_iwide(value: IWide) -> Self {
        Self::from_i128(value as i128)
    }

    /// Convert the 256-bit signed integer to an `u8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u8(&self) -> u8 {
        self.as_u128() as u8
    }

    /// Convert the 256-bit signed integer to an `u16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u16(&self) -> u16 {
        self.as_u128() as u16
    }

    /// Convert the 256-bit signed integer to an `u32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u32(&self) -> u32 {
        self.as_u128() as u32
    }

    /// Convert the 256-bit signed integer to an `u64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u64(&self) -> u64 {
        self.as_u128() as u64
    }

    /// Convert the 256-bit signed integer to an `u128`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u128(&self) -> u128 {
        math::as_unarrow_i128(self.low(), self.high())
    }

    /// Convert the 256-bit signed integer to an `u256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u256(&self) -> u256 {
        let (lo, hi) = math::wide_cast_i128(self.low(), self.high());
        u256::new(lo, hi)
    }

    /// Convert the 256-bit signed integer to an unsigned limb, as if by an `as`
    /// cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn as_ulimb(&self) -> ULimb {
        self.as_u128() as ULimb
    }

    /// Convert the 256-bit signed integer to an unsigned wide type, as if by an
    /// `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn as_uwide(&self) -> UWide {
        self.as_u128() as UWide
    }

    /// Convert the 256-bit signed integer to an `i8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i8(&self) -> i8 {
        self.as_i128() as i8
    }

    /// Convert the 256-bit signed integer to an `i16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i16(&self) -> i16 {
        self.as_i128() as i16
    }

    /// Convert the 256-bit signed integer to an `i32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i32(&self) -> i32 {
        self.as_i128() as i32
    }

    /// Convert the 256-bit signed integer to an `i64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i64(&self) -> i64 {
        self.as_i128() as i64
    }

    /// Convert the 256-bit signed integer to an `i128`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i128(&self) -> i128 {
        math::as_inarrow_i128(self.low(), self.high())
    }

    /// Convert the 256-bit signed integer to an `i256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i256(&self) -> i256 {
        *self
    }

    /// Convert the 256-bit signed integer to a signed limb, as if by an `as`
    /// cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn as_ilimb(&self) -> ILimb {
        self.as_i128() as ILimb
    }

    /// Convert the 256-bit signed integer to a signed wide type, as if by an
    /// `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn as_iwide(&self) -> IWide {
        self.as_i128() as IWide
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn add_uwide(self, n: UWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_add_uwide(n)
        } else {
            match self.checked_add_uwide(n) {
                Some(v) => v,
                _ => panic!("attempt to add with overflow"),
            }
        }
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn wrapping_add_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_add_uwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn overflowing_add_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_add_uwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn checked_add_uwide(self, n: UWide) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add_uwide(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Add the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn add_iwide(self, n: IWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_add_iwide(n)
        } else {
            match self.checked_add_iwide(n) {
                Some(v) => v,
                _ => panic!("attempt to add with overflow"),
            }
        }
    }

    /// Add the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn wrapping_add_iwide(self, n: IWide) -> Self {
        let (lo, hi) = math::wrapping_add_iwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Add the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn overflowing_add_iwide(self, n: IWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_add_iwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Add the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn checked_add_iwide(self, n: IWide) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add_iwide(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn sub_uwide(self, n: UWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_sub_uwide(n)
        } else {
            match self.checked_sub_uwide(n) {
                Some(v) => v,
                _ => panic!("attempt to subtract with overflow"),
            }
        }
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn wrapping_sub_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_sub_uwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn overflowing_sub_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_sub_uwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn checked_sub_uwide(self, n: UWide) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub_uwide(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Subtract the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn sub_iwide(self, n: IWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_sub_iwide(n)
        } else {
            match self.checked_sub_iwide(n) {
                Some(v) => v,
                _ => panic!("attempt to subtract with overflow"),
            }
        }
    }

    /// Subtract the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn wrapping_sub_iwide(self, n: IWide) -> Self {
        let (lo, hi) = math::wrapping_sub_iwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn overflowing_sub_iwide(self, n: IWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_sub_iwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn checked_sub_iwide(self, n: IWide) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub_iwide(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn mul_uwide(self, n: UWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul_uwide(n)
        } else {
            match self.checked_mul_uwide(n) {
                Some(v) => v,
                _ => panic!("attempt to multiply with overflow"),
            }
        }
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn wrapping_mul_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_mul_uwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_uwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn checked_mul_uwide(self, n: UWide) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul_uwide(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Multiply the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn mul_iwide(self, n: IWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul_iwide(n)
        } else {
            match self.checked_mul_iwide(n) {
                Some(v) => v,
                _ => panic!("attempt to multiply with overflow"),
            }
        }
    }

    /// Multiply the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn wrapping_mul_iwide(self, n: IWide) -> Self {
        let (lo, hi) = math::wrapping_mul_iwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_iwide(self, n: IWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_iwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn checked_mul_iwide(self, n: IWide) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul_iwide(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn mul_ulimb(self, n: ULimb) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul_ulimb(n)
        } else {
            match self.checked_mul_ulimb(n) {
                Some(v) => v,
                _ => panic!("attempt to multiply with overflow"),
            }
        }
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn wrapping_mul_ulimb(self, n: ULimb) -> Self {
        let (lo, hi) = math::wrapping_mul_ulimb_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_ulimb(self, n: ULimb) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_ulimb_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn checked_mul_ulimb(self, n: ULimb) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul_ulimb(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Multiply the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn mul_ilimb(self, n: ILimb) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul_ilimb(n)
        } else {
            match self.checked_mul_ilimb(n) {
                Some(v) => v,
                _ => panic!("attempt to multiply with overflow"),
            }
        }
    }

    /// Multiply the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn wrapping_mul_ilimb(self, n: ILimb) -> Self {
        let (lo, hi) = math::wrapping_mul_ilimb_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_ilimb(self, n: ILimb) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_ilimb_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn checked_mul_ilimb(self, n: ILimb) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul_ilimb(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Div/Rem operation on a 256-bit integer.
    ///
    /// This allows storing of both the quotient and remainder without
    /// making repeated calls.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    #[inline(always)]
    pub fn div_rem(self, n: Self) -> (Self, Self) {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_rem(n)
        } else {
            self.checked_div_rem(n).expect("attempt to divide with overflow")
        }
    }

    /// Div/Rem operation on a 256-bit integer.
    ///
    /// This allows storing of both the quotient and remainder without
    /// making repeated calls.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    #[inline]
    pub fn wrapping_div_rem(self, n: Self) -> (Self, Self) {
        // NOTE: Our algorithm assumes little-endian order, which we might not have.
        // So, we transmute to LE order prior to the call.
        // Do division as positive numbers, and if `lhs.is_sign_negative() ^
        // rhs.is_sign_negative()`, then we can inver the sign
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let y = n.wrapping_abs().as_u256().to_le_limbs();

        // get our unsigned division product
        let (div, rem) = math::div_rem_full(&x, &y);
        let mut div = u256::from_le_limbs(div).as_i256();
        let mut rem = u256::from_le_limbs(rem).as_i256();

        // convert to our correct signs, get the product
        if self.is_negative() != n.is_negative() {
            div = div.wrapping_neg();
        }
        if self.is_negative() {
            rem = rem.wrapping_neg();
        }

        (div, rem)
    }

    /// Div/Rem operation on a 256-bit integer.
    ///
    /// This allows storing of both the quotient and remainder without
    /// making repeated calls.
    #[inline]
    pub fn checked_div_rem(self, n: Self) -> Option<(Self, Self)> {
        if n == Self::from_u8(0) {
            None
        } else {
            Some(self.wrapping_div_rem(n))
        }
    }

    /// Div/Rem operation on a 256-bit integer.
    ///
    /// This allows storing of both the quotient and remainder without
    /// making repeated calls.
    #[inline]
    pub fn overflowing_div_rem(self, n: Self) -> ((Self, Self), bool) {
        if n == Self::from_u8(0) {
            ((Self::MAX, Self::from_u8(0)), true)
        } else {
            (self.wrapping_div_rem(n), false)
        }
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`div_rem`]
    /// or [`div_rem_ulimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`div_rem`]: Self::div_rem
    /// [`div_rem_ulimb`]: Self::div_rem_ulimb
    #[inline]
    pub fn div_rem_uwide(self, n: UWide) -> (Self, UWide) {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_rem_uwide(n)
        } else {
            self.checked_div_rem_uwide(n).expect("attempt to divide by zero")
        }
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_div_rem`]
    /// or [`wrapping_div_rem_ulimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`wrapping_div_rem`]: Self::wrapping_div_rem
    /// [`wrapping_div_rem_ulimb`]: Self::wrapping_div_rem_ulimb
    #[inline]
    pub fn wrapping_div_rem_uwide(self, n: UWide) -> (Self, UWide) {
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let (div, rem) = math::div_rem_wide(&x, n);
        let div = u256::from_le_limbs(div).as_i256();
        // rem is always positive: `-65 % 64` is 63
        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`checked_div_rem`]
    /// or [`checked_div_rem_ulimb`] if possible.
    ///
    /// [`checked_div_rem`]: Self::checked_div_rem
    /// [`checked_div_rem_ulimb`]: Self::checked_div_rem_ulimb
    #[inline]
    pub fn checked_div_rem_uwide(self, n: UWide) -> Option<(Self, UWide)> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_rem_uwide(n))
        }
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`overflowing_div_rem`]
    /// or [`overflowing_div_rem_ulimb`] if possible.
    ///
    /// [`overflowing_div_rem`]: Self::overflowing_div_rem
    /// [`overflowing_div_rem_ulimb`]: Self::overflowing_div_rem_ulimb
    #[inline]
    pub fn overflowing_div_rem_uwide(self, n: UWide) -> ((Self, UWide), bool) {
        if n == 0 {
            ((Self::MAX, 0), true)
        } else {
            (self.wrapping_div_rem_uwide(n), false)
        }
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`div_rem`]
    /// or [`div_rem_ilimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`div_rem`]: Self::div_rem
    /// [`div_rem_ilimb`]: Self::div_rem_ilimb
    #[inline]
    pub fn div_rem_iwide(self, n: IWide) -> (Self, IWide) {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_rem_iwide(n)
        } else {
            self.checked_div_rem_iwide(n).expect("attempt to divide by zero")
        }
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_div_rem`]
    /// or [`wrapping_div_rem_ilimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`wrapping_div_rem`]: Self::wrapping_div_rem
    /// [`wrapping_div_rem_ilimb`]: Self::wrapping_div_rem_ilimb
    #[inline]
    pub fn wrapping_div_rem_iwide(self, n: IWide) -> (Self, IWide) {
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let (div, rem) = math::div_rem_wide(&x, n.wrapping_abs() as UWide);
        let mut div = u256::from_le_limbs(div).as_i256();
        let mut rem = rem as IWide;

        // convert to our correct signs, get the product
        if self.is_negative() != n.is_negative() {
            div = div.wrapping_neg();
        }
        if self.is_negative() {
            rem = rem.wrapping_neg();
        }

        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`checked_div_rem`]
    /// or [`checked_div_rem_ulimb`] if possible.
    ///
    /// [`checked_div_rem`]: Self::checked_div_rem
    /// [`checked_div_rem_ulimb`]: Self::checked_div_rem_ulimb
    #[inline]
    pub fn checked_div_rem_iwide(self, n: IWide) -> Option<(Self, IWide)> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_rem_iwide(n))
        }
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`overflowing_div_rem`]
    /// or [`overflowing_div_rem_ulimb`] if possible.
    ///
    /// [`overflowing_div_rem`]: Self::overflowing_div_rem
    /// [`overflowing_div_rem_ulimb`]: Self::overflowing_div_rem_ulimb
    #[inline]
    pub fn overflowing_div_rem_iwide(self, n: IWide) -> ((Self, IWide), bool) {
        if n == 0 {
            ((Self::MAX, 0), true)
        } else {
            (self.wrapping_div_rem_iwide(n), false)
        }
    }

    /// Div the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`div`]
    /// or [`div_ulimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`div`]: Self::div
    /// [`div_ulimb`]: Self::div_ulimb
    #[inline(always)]
    pub fn div_uwide(self, n: UWide) -> Self {
        self.div_rem_uwide(n).0
    }

    /// Div the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_div`]
    /// or [`wrapping_div_ulimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`wrapping_div`]: Self::wrapping_div
    /// [`wrapping_div_ulimb`]: Self::wrapping_div_ulimb
    #[inline(always)]
    pub fn wrapping_div_uwide(self, n: UWide) -> Self {
        self.wrapping_div_rem_uwide(n).0
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`checked_div`]
    /// or [`checked_div_ulimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`checked_div`]: Self::checked_div
    /// [`checked_div_ulimb`]: Self::checked_div_ulimb
    #[inline(always)]
    pub fn checked_div_uwide(self, n: UWide) -> Option<Self> {
        Some(self.checked_div_rem_uwide(n)?.0)
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`overflowing_div`]
    /// or [`overflowing_div_ulimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`overflowing_div`]: Self::overflowing_div
    /// [`overflowing_div_ulimb`]: Self::overflowing_div_ulimb
    #[inline(always)]
    pub fn overflowing_div_uwide(self, n: UWide) -> (Self, bool) {
        let (value, overflowed) = self.overflowing_div_rem_uwide(n);
        (value.0, overflowed)
    }

    /// Div the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`div`]
    /// or [`div_ilimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`div`]: Self::div
    /// [`div_ilimb`]: Self::div_ilimb
    #[inline(always)]
    pub fn div_iwide(self, n: IWide) -> Self {
        self.div_rem_iwide(n).0
    }

    /// Div the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_div`]
    /// or [`wrapping_div_ilimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`wrapping_div`]: Self::wrapping_div
    /// [`wrapping_div_ilimb`]: Self::wrapping_div_ilimb
    #[inline(always)]
    pub fn wrapping_div_iwide(self, n: IWide) -> Self {
        self.wrapping_div_rem_iwide(n).0
    }

    /// Div the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`checked_div`]
    /// or [`checked_div_ilimb`] if possible.
    ///
    /// [`checked_div`]: Self::checked_div
    /// [`checked_div_ilimb`]: Self::checked_div_ilimb
    #[inline(always)]
    pub fn checked_div_iwide(self, n: IWide) -> Option<Self> {
        Some(self.checked_div_rem_iwide(n)?.0)
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`overflowing_div`]
    /// or [`overflowing_div_ilimb`] if possible.
    ///
    /// [`overflowing_div`]: Self::overflowing_div
    /// [`overflowing_div_ilimb`]: Self::overflowing_div_ilimb
    #[inline(always)]
    pub fn overflowing_div_iwide(self, n: IWide) -> (Self, bool) {
        let (value, overflowed) = self.overflowing_div_rem_iwide(n);
        (value.0, overflowed)
    }

    /// Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`rem`]
    /// or [`rem_ulimb`] if possible.
    ///
    /// [`rem`]: Self::rem
    /// [`rem_ulimb`]: Self::rem_ulimb
    #[inline(always)]
    pub fn rem_uwide(self, n: UWide) -> UWide {
        self.wrapping_div_rem_uwide(n).1
    }

    /// Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_rem`]
    /// or [`wrapping_rem_ulimb`] if possible.
    ///
    /// [`wrapping_rem`]: Self::wrapping_rem
    /// [`wrapping_rem_ulimb`]: Self::wrapping_rem_ulimb
    #[inline(always)]
    pub fn wrapping_rem_uwide(self, n: UWide) -> UWide {
        self.wrapping_div_rem_uwide(n).1
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`checked_rem`]
    /// or [`checked_rem_ulimb`] if possible.
    ///
    /// [`checked_rem`]: Self::checked_rem
    /// [`checked_rem_ulimb`]: Self::checked_rem_ulimb
    #[inline(always)]
    pub fn checked_rem_uwide(self, n: UWide) -> Option<UWide> {
        Some(self.checked_div_rem_uwide(n)?.1)
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`overflowing_rem`]
    /// or [`overflowing_rem_ulimb`] if possible.
    ///
    /// [`overflowing_rem`]: Self::overflowing_rem
    /// [`overflowing_rem_ulimb`]: Self::overflowing_rem_ulimb
    #[inline(always)]
    pub fn overflowing_rem_uwide(self, n: UWide) -> (UWide, bool) {
        let (value, overflowed) = self.overflowing_div_rem_uwide(n);
        (value.1, overflowed)
    }

    /// Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`rem`]
    /// or [`rem_ilimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`rem`]: Self::rem
    /// [`rem_ilimb`]: Self::rem_ilimb
    #[inline(always)]
    pub fn rem_iwide(self, n: IWide) -> IWide {
        self.div_rem_iwide(n).1
    }

    /// Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_rem`]
    /// or [`wrapping_rem_ilimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`wrapping_rem`]: Self::wrapping_rem
    /// [`wrapping_rem_ilimb`]: Self::wrapping_rem_ilimb
    #[inline(always)]
    pub fn wrapping_rem_iwide(self, n: IWide) -> IWide {
        self.wrapping_div_rem_iwide(n).1
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`checked_rem`]
    /// or [`checked_rem_ilimb`] if possible.
    ///
    /// [`checked_rem`]: Self::checked_rem
    /// [`checked_rem_ilimb`]: Self::checked_rem_ilimb
    #[inline(always)]
    pub fn checked_rem_iwide(self, n: IWide) -> Option<IWide> {
        Some(self.checked_div_rem_iwide(n)?.1)
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`overflowing_rem`]
    /// or [`overflowing_rem_ilimb`] if possible.
    ///
    /// [`overflowing_rem`]: Self::overflowing_rem
    /// [`overflowing_rem_ilimb`]: Self::overflowing_rem_ilimb
    #[inline(always)]
    pub fn overflowing_rem_iwide(self, n: IWide) -> (IWide, bool) {
        let (value, overflowed) = self.overflowing_div_rem_iwide(n);
        (value.1, overflowed)
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline]
    pub fn div_rem_ulimb(self, n: ULimb) -> (Self, ULimb) {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_rem_ulimb(n)
        } else {
            self.checked_div_rem_ulimb(n).expect("attempt to divide by zero")
        }
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do. This always
    /// wraps, which can never happen in practice.
    #[inline]
    pub fn wrapping_div_rem_ulimb(self, n: ULimb) -> (Self, ULimb) {
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let (div, rem) = math::div_rem_limb(&x, n);
        let div = u256::from_le_limbs(div).as_i256();
        // rem is always positive: `-65 % 64` is 63
        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline]
    pub fn checked_div_rem_ulimb(self, n: ULimb) -> Option<(Self, ULimb)> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_rem_ulimb(n))
        }
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline]
    pub fn overflowing_div_rem_ulimb(self, n: ULimb) -> ((Self, ULimb), bool) {
        if n == 0 {
            ((Self::MAX, 0), true)
        } else {
            (self.wrapping_div_rem_ulimb(n), false)
        }
    }

    /// Div/Rem the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline]
    pub fn div_rem_ilimb(self, n: ILimb) -> (Self, ILimb) {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_rem_ilimb(n)
        } else {
            self.checked_div_rem_ilimb(n).expect("attempt to divide by zero")
        }
    }

    /// Div/Rem the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do. This always
    /// wraps, which can never happen in practice.
    #[inline]
    pub fn wrapping_div_rem_ilimb(self, n: ILimb) -> (Self, ILimb) {
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let (div, rem) = math::div_rem_limb(&x, n.wrapping_abs() as ULimb);
        let mut div = u256::from_le_limbs(div).as_i256();
        let mut rem = rem as ILimb;

        // convert to our correct signs, get the product
        if self.is_negative() != n.is_negative() {
            div = div.wrapping_neg();
        }
        if self.is_negative() {
            rem = rem.wrapping_neg();
        }

        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline]
    pub fn checked_div_rem_ilimb(self, n: ILimb) -> Option<(Self, ILimb)> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_rem_ilimb(n))
        }
    }

    /// Div/Rem the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline]
    pub fn overflowing_div_rem_ilimb(self, n: ILimb) -> ((Self, ILimb), bool) {
        if n == 0 {
            ((Self::MAX, 0), true)
        } else {
            (self.wrapping_div_rem_ilimb(n), false)
        }
    }

    /// Div the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn div_ulimb(self, n: ULimb) -> Self {
        self.div_rem_ulimb(n).0
    }

    /// Div the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_div_ulimb(self, n: ULimb) -> Self {
        self.wrapping_div_rem_ulimb(n).0
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_ulimb(self, n: ULimb) -> Option<Self> {
        Some(self.checked_div_rem_ulimb(n)?.0)
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_ulimb(self, n: ULimb) -> (Self, bool) {
        let (value, overflowed) = self.overflowing_div_rem_ulimb(n);
        (value.0, overflowed)
    }

    /// Div the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn div_ilimb(self, n: ILimb) -> Self {
        self.div_rem_ilimb(n).0
    }

    /// Div the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_div_ilimb(self, n: ILimb) -> Self {
        self.wrapping_div_rem_ilimb(n).0
    }

    /// Div/Rem the 256-bit integer by a 64-bit signed factor.
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_ilimb(self, n: ILimb) -> Option<Self> {
        Some(self.checked_div_rem_ilimb(n)?.0)
    }

    /// Div/Rem the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_ilimb(self, n: ILimb) -> (Self, bool) {
        let (value, overflowed) = self.overflowing_div_rem_ilimb(n);
        (value.0, overflowed)
    }

    /// Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn rem_ulimb(self, n: ULimb) -> ULimb {
        self.wrapping_div_rem_ulimb(n).1
    }

    /// Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_rem_ulimb(self, n: ULimb) -> ULimb {
        self.wrapping_div_rem_ulimb(n).1
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_rem_ulimb(self, n: ULimb) -> Option<ULimb> {
        Some(self.checked_div_rem_ulimb(n)?.1)
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_rem_ulimb(self, n: ULimb) -> (ULimb, bool) {
        let (value, overflowed) = self.overflowing_div_rem_ulimb(n);
        (value.1, overflowed)
    }

    /// Rem the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn rem_ilimb(self, n: ILimb) -> ILimb {
        self.div_rem_ilimb(n).1
    }

    /// Rem the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_rem_ilimb(self, n: ILimb) -> ILimb {
        self.wrapping_div_rem_ilimb(n).1
    }

    /// Div/Rem the 256-bit integer by a 64-bit signed factor.
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_rem_ilimb(self, n: ILimb) -> Option<ILimb> {
        Some(self.checked_div_rem_ilimb(n)?.1)
    }

    /// Div/Rem the 256-bit integer by a 64-bit signed factor.
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_rem_ilimb(self, n: ILimb) -> (ILimb, bool) {
        let (value, overflowed) = self.overflowing_div_rem_ilimb(n);
        (value.1, overflowed)
    }
}

// These are implementations for nightly-only APIs.
impl i256 {
    /// Returns the bit pattern of `self` reinterpreted as an unsigned integer
    /// of the same size.
    ///
    /// This produces the same result as an `as` cast, but ensures that the
    /// bit-width remains the same.
    ///
    /// See [`i128::cast_unsigned`].
    #[inline(always)]
    pub const fn cast_unsigned(self) -> u256 {
        self.as_u256()
    }

    /// Calculates `self` + `rhs` + `carry` and returns a tuple containing
    /// the sum and the output carry.
    ///
    /// Performs "ternary addition" of two integer operands and a carry-in
    /// bit, and returns an output integer and a carry-out bit. This allows
    /// chaining together multiple additions to create a wider addition, and
    /// can be useful for bignum addition.
    ///
    /// See [`i128::carrying_add`].
    #[inline]
    #[must_use]
    pub const fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
        let (a, b) = self.overflowing_add(rhs);
        let (c, d) = a.overflowing_add(Self::from_u8(carry as u8));
        (c, b | d)
    }

    /// Calculates `self` &minus; `rhs` &minus; `borrow` and returns a tuple
    /// containing the difference and the output borrow.
    ///
    /// Performs "ternary subtraction" by subtracting both an integer
    /// operand and a borrow-in bit from `self`, and returns an output
    /// integer and a borrow-out bit. This allows chaining together multiple
    /// subtractions to create a wider subtraction, and can be useful for
    /// bignum subtraction.
    ///
    /// See [`i128::borrowing_sub`].
    #[inline]
    #[must_use]
    pub const fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
        let (a, b) = self.overflowing_sub(rhs);
        let (c, d) = a.overflowing_sub(Self::from_u8(borrow as u8));
        (c, b | d)
    }

    /// Strict integer addition. Computes `self + rhs`, panicking
    /// if overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_add`].
    #[inline]
    #[must_use]
    pub const fn strict_add(self, rhs: Self) -> Self {
        match self.checked_add(rhs) {
            Some(v) => v,
            None => panic!("attempt to add with overflow"),
        }
    }

    /// Strict addition with an unsigned integer. Computes `self + rhs`,
    /// panicking if overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_add_unsigned`].
    #[inline]
    #[must_use]
    pub const fn strict_add_unsigned(self, rhs: u256) -> Self {
        match self.checked_add_unsigned(rhs) {
            Some(v) => v,
            None => panic!("attempt to add with overflow"),
        }
    }

    /// Strict integer subtraction. Computes `self - rhs`, panicking if
    /// overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_sub`].
    #[inline]
    #[must_use]
    pub const fn strict_sub(self, rhs: Self) -> Self {
        match self.checked_sub(rhs) {
            Some(v) => v,
            None => panic!("attempt to subtract with overflow"),
        }
    }

    /// Strict subtraction with an unsigned integer. Computes `self - rhs`,
    /// panicking if overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_sub_unsigned`].
    #[inline]
    #[must_use]
    pub const fn strict_sub_unsigned(self, rhs: u256) -> Self {
        match self.checked_sub_unsigned(rhs) {
            Some(v) => v,
            None => panic!("attempt to subtract with overflow"),
        }
    }

    /// Strict integer multiplication. Computes `self * rhs`, panicking if
    /// overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_mul`].
    #[inline]
    #[must_use]
    pub const fn strict_mul(self, rhs: Self) -> Self {
        match self.checked_mul(rhs) {
            Some(v) => v,
            None => panic!("attempt to multiply with overflow"),
        }
    }

    /// Strict integer division. Computes `self / rhs`, panicking
    /// if overflow occurred.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// The only case where such an overflow can occur is when one divides `MIN
    /// / -1` on a signed type (where `MIN` is the negative minimal value
    /// for the type.
    ///
    /// See [`i128::strict_div`].
    #[inline]
    #[must_use]
    pub fn strict_div(self, rhs: Self) -> Self {
        match self.checked_div(rhs) {
            Some(v) => v,
            None => panic!("attempt to divide with overflow"),
        }
    }

    /// Strict Euclidean division. Computes `self.div_euclid(rhs)`, panicking
    /// if overflow occurred.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// The only case where such an overflow can occur is when one divides `MIN
    /// / -1` on a signed type (where `MIN` is the negative minimal value
    /// for the type); this is equivalent to `-MIN`, a positive value
    /// that is too large to represent in the type.
    ///
    /// See [`i128::strict_div_euclid`].
    #[inline]
    #[must_use]
    pub fn strict_div_euclid(self, rhs: Self) -> Self {
        match self.checked_div_euclid(rhs) {
            Some(v) => v,
            None => panic!("attempt to divide with overflow"),
        }
    }

    /// Strict integer remainder. Computes `self % rhs`, panicking if
    /// the division results in overflow.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// The only case where such an overflow can occur is `x % y` for `MIN / -1`
    /// on a signed type (where `MIN` is the negative minimal value), which
    /// is invalid due to implementation artifacts.
    ///
    /// See [`i128::strict_rem`].
    #[inline]
    #[must_use]
    pub fn strict_rem(self, rhs: Self) -> Self {
        match self.checked_rem(rhs) {
            Some(v) => v,
            None => panic!("attempt to divide with overflow"),
        }
    }

    /// Strict Euclidean remainder. Computes `self.rem_euclid(rhs)`, panicking
    /// if the division results in overflow.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// The only case where such an overflow can occur is `x % y` for `MIN / -1`
    /// on a signed type (where `MIN` is the negative minimal value), which
    /// is invalid due to implementation artifacts.
    ///
    /// See [`i128::strict_rem_euclid`].
    #[inline]
    #[must_use]
    pub fn strict_rem_euclid(self, rhs: Self) -> Self {
        match self.checked_rem_euclid(rhs) {
            Some(v) => v,
            None => panic!("attempt to divide with overflow"),
        }
    }

    /// Strict negation. Computes `-self`, panicking if `self == MIN`.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_neg`].
    #[inline]
    #[must_use]
    pub const fn strict_neg(self) -> Self {
        match self.checked_neg() {
            Some(v) => v,
            None => panic!("attempt to negate with overflow"),
        }
    }

    /// Strict absolute value. Computes `self.abs()`, panicking if
    /// `self == MIN`.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_abs`].
    #[inline]
    #[must_use]
    pub const fn strict_abs(self) -> Self {
        match self.checked_abs() {
            Some(v) => v,
            None => panic!("attempt to negate with overflow"),
        }
    }

    /// Strict exponentiation. Computes `self.pow(exp)`, panicking if
    /// overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_pow`].
    #[inline]
    #[must_use]
    pub const fn strict_pow(self, rhs: u32) -> Self {
        match self.checked_pow(rhs) {
            Some(v) => v,
            None => panic!("attempt to multiply with overflow"),
        }
    }

    /// Strict shift left. Computes `self << rhs`, panicking if `rhs` is larger
    /// than or equal to the number of bits in `self`.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_shl`].
    #[inline]
    #[must_use]
    pub const fn strict_shl(self, rhs: u32) -> Self {
        match self.checked_shl(rhs) {
            Some(v) => v,
            None => panic!("attempt to shift left with overflow"),
        }
    }

    /// Strict shift right. Computes `self >> rhs`, panicking `rhs` is
    /// larger than or equal to the number of bits in `self`.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`i128::strict_shr`].
    #[inline]
    #[must_use]
    pub const fn strict_shr(self, rhs: u32) -> Self {
        match self.checked_shr(rhs) {
            Some(v) => v,
            None => panic!("attempt to shift right with overflow"),
        }
    }

    /// Calculates the middle point of `self` and `rhs`.
    ///
    /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a
    /// sufficiently-large unsigned integral type. This implies that the
    /// result is always rounded towards negative infinity and that no
    /// overflow will ever occur.
    ///
    /// See [`i128::midpoint`].
    #[inline]
    #[must_use]
    pub const fn midpoint(self, rhs: Self) -> Self {
        // Use the well known branchless algorithm from Hacker's Delight to compute
        // `(a + b) / 2` without overflowing: `((a ^ b) >> 1) + (a & b)`.
        let xor = bitxor(self, rhs);
        let (lo, hi) = math::shr_i128(xor.low(), xor.high(), 1);
        let t = Self::new(lo, hi).wrapping_add(bitand(self, rhs));
        // Except that it fails for integers whose sum is an odd negative number as
        // their floor is one less than their average. So we adjust the result.
        let is_negative = Self::from_u8(t.is_negative() as u8);
        t.wrapping_add(bitand(is_negative, xor))
    }

    /// Unchecked integer addition. Computes `self + rhs`, assuming overflow
    /// cannot occur.
    ///
    /// Calling `x.unchecked_add(y)` is semantically equivalent to calling
    /// `x.`[`checked_add`]`(y).`[`unwrap_unchecked`]`()`.
    ///
    /// If you're just trying to avoid the panic in debug mode, then **do not**
    /// use this.  Instead, you're looking for [`wrapping_add`].
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when the value overflows.
    ///
    /// See [`i128::unchecked_add`].
    ///
    /// [`checked_add`]: Self::checked_add
    /// [`wrapping_add`]: Self::wrapping_add
    /// [`unwrap_unchecked`]: Option::unwrap_unchecked
    #[must_use]
    #[inline(always)]
    pub unsafe fn unchecked_add(self, rhs: Self) -> Self {
        match self.checked_add(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unchecked integer subtraction. Computes `self - rhs`, assuming overflow
    /// cannot occur.
    ///
    /// Calling `x.unchecked_sub(y)` is semantically equivalent to calling
    /// `x.`[`checked_sub`]`(y).`[`unwrap_unchecked`]`()`.
    ///
    /// If you're just trying to avoid the panic in debug mode, then **do not**
    /// use this.  Instead, you're looking for [`wrapping_sub`].
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when the value overflows.
    ///
    /// See [`i128::unchecked_sub`].
    ///
    /// [`checked_sub`]: Self::checked_sub
    /// [`wrapping_sub`]: Self::wrapping_sub
    /// [`unwrap_unchecked`]: Option::unwrap_unchecked
    #[must_use]
    #[inline(always)]
    pub unsafe fn unchecked_sub(self, rhs: Self) -> Self {
        match self.checked_sub(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unchecked integer multiplication. Computes `self * rhs`, assuming
    /// overflow cannot occur.
    ///
    /// Calling `x.unchecked_mul(y)` is semantically equivalent to calling
    /// `x.`[`checked_mul`]`(y).`[`unwrap_unchecked`]`()`.
    ///
    /// If you're just trying to avoid the panic in debug mode, then **do not**
    /// use this.  Instead, you're looking for [`wrapping_mul`].
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when the value overflows.
    ///
    /// See [`i128::unchecked_mul`].
    ///
    /// [`checked_mul`]: Self::checked_mul
    /// [`wrapping_mul`]: Self::wrapping_mul
    /// [`unwrap_unchecked`]: Option::unwrap_unchecked
    #[must_use]
    #[inline(always)]
    pub unsafe fn unchecked_mul(self, rhs: Self) -> Self {
        match self.checked_mul(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unchecked negation. Computes `-self`, assuming overflow cannot occur.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when the value overflows.
    ///
    /// See [`i128::unchecked_neg`].
    #[must_use]
    #[inline(always)]
    pub unsafe fn unchecked_neg(self) -> Self {
        match self.checked_neg() {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unchecked shift left. Computes `self << rhs`, assuming that
    /// `rhs` is less than the number of bits in `self`.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `rhs` is larger than
    /// or equal to the number of bits in `self`,
    /// i.e. when [`checked_shl`] would return `None`.
    ///
    /// See [`i128::unchecked_shl`].
    ///
    /// [`checked_shl`]: Self::checked_shl
    #[must_use]
    #[inline(always)]
    pub const unsafe fn unchecked_shl(self, rhs: u32) -> Self {
        match self.checked_shl(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unchecked shift right. Computes `self >> rhs`, assuming that
    /// `rhs` is less than the number of bits in `self`.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `rhs` is larger than
    /// or equal to the number of bits in `self`,
    /// i.e. when [`checked_shr`] would return `None`.
    ///
    /// See [`i128::unchecked_shr`].
    ///
    /// [`checked_shr`]: Self::checked_shr
    #[must_use]
    #[inline(always)]
    pub const unsafe fn unchecked_shr(self, rhs: u32) -> Self {
        match self.checked_shr(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unbounded shift left. Computes `self << rhs`, without bounding the value
    /// of `rhs`.
    ///
    /// If `rhs` is larger or equal to the number of bits in `self`,
    /// the entire value is shifted out, and `0` is returned.
    #[inline]
    #[must_use]
    pub const fn unbounded_shl(self, rhs: u32) -> Self {
        if rhs < Self::BITS {
            self.wrapping_shl(rhs)
        } else {
            Self::from_u8(0)
        }
    }

    /// Unbounded shift right. Computes `self >> rhs`, without bounding the
    /// value of `rhs`.
    ///
    /// If `rhs` is larger or equal to the number of bits in `self`,
    /// the entire value is shifted out, which yields `0` for a positive number,
    /// and `-1` for a negative number.
    #[inline]
    #[must_use]
    pub const fn unbounded_shr(self, rhs: u32) -> Self {
        if rhs < Self::BITS {
            self.wrapping_shr(rhs)
        } else {
            Self::from_u8(0)
        }
    }
}

impl Add for i256 {
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

op_impl!(i256, Add, AddAssign, add, add_assign);

impl fmt::Binary for i256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: Binary for negative numbers uses wrapping formats.
        fmt::Binary::fmt(&self.as_u256(), f)
    }
}

impl BitAnd for i256 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        bitand(self, rhs)
    }
}

op_impl!(i256, BitAnd, BitAndAssign, bitand, bitand_assign);

impl BitOr for i256 {
    type Output = i256;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        bitor(self, rhs)
    }
}

op_impl!(i256, BitOr, BitOrAssign, bitor, bitor_assign);

impl BitXor for i256 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self::Output {
        bitxor(self, rhs)
    }
}

op_impl!(i256, BitXor, BitXorAssign, bitxor, bitxor_assign);

impl fmt::Debug for i256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for i256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.is_negative() {
            write!(f, "-")?;
        } else if f.sign_plus() {
            write!(f, "+")?;
        }
        fmt::Display::fmt(&self.unsigned_abs(), f)
    }
}

impl Div for i256 {
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

op_impl!(i256, Div, DivAssign, div, div_assign);

impl From<bool> for i256 {
    #[inline(always)]
    fn from(small: bool) -> Self {
        Self::new(small as u128, 0)
    }
}

impl From<char> for i256 {
    #[inline(always)]
    fn from(c: char) -> Self {
        Self::new(c as u128, 0)
    }
}

from_impl!(i256, u8, from_u8);
from_impl!(i256, u16, from_u16);
from_impl!(i256, u32, from_u32);
from_impl!(i256, u64, from_u64);
from_impl!(i256, u128, from_u128);
from_impl!(i256, i8, from_i8);
from_impl!(i256, i16, from_i16);
from_impl!(i256, i32, from_i32);
from_impl!(i256, i64, from_i64);
from_impl!(i256, i128, from_i128);

impl FromStr for i256 {
    type Err = ParseIntError;

    /// Parses a string s to return a value of this type.
    ///
    /// This is not optimized, since all optimization is done in
    /// theimplementation.
    #[inline]
    fn from_str(src: &str) -> Result<i256, ParseIntError> {
        // up to 39 digits can be stored in a `u128`, so less is always valid
        // meanwhile, 78 is good for all 256-bit integers. 32-bit architectures
        // on average have poor support for 128-bit operations so we try to use `u64`.
        if (cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32"))
            && src.len() < 19
        {
            Ok(i256::from_i64(i64::from_str(src)?))
        } else if src.len() < 39 {
            Ok(i256::from_i128(i128::from_str(src)?))
        } else {
            i256::from_str_radix(src, 10)
        }
    }
}

impl fmt::LowerExp for i256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.is_negative() {
            write!(f, "-")?;
        } else if f.sign_plus() {
            write!(f, "+")?;
        }
        fmt::LowerExp::fmt(&self.abs().as_u256(), f)
    }
}

impl fmt::LowerHex for i256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: LowerHex for negative numbers uses wrapping formats.
        fmt::LowerHex::fmt(&self.as_u256(), f)
    }
}

impl Mul for i256 {
    type Output = i256;

    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul(rhs)
        } else {
            self.checked_mul(rhs).expect("attempt to multiply with overflow")
        }
    }
}

op_impl!(i256, Mul, MulAssign, mul, mul_assign);

impl Neg for i256 {
    type Output = Self;

    #[inline(always)]
    fn neg(self) -> Self::Output {
        neg(self)
    }
}

ref_impl!(i256, Neg, neg);

impl Not for i256 {
    type Output = i256;

    #[inline(always)]
    fn not(self) -> Self::Output {
        not(self)
    }
}

ref_impl!(i256, Not, not);

impl fmt::Octal for i256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: Octal for negative numbers uses wrapping formats.
        fmt::Octal::fmt(&self.as_u256(), f)
    }
}

impl Ord for i256 {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        cmp(*self, *other)
    }
}

impl PartialOrd for i256 {
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

impl Rem for i256 {
    type Output = i256;

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

op_impl!(i256, Rem, RemAssign, rem, rem_assign);

macro_rules! shift_const_impl {
    (@shl $value:ident, $shift:ident) => {{
        let (lo, hi) = math::shl_i128($value.low(), $value.high(), $shift as u32);
        Self::new(lo, hi)
    }};

    (@shr $value:ident, $shift:ident) => {{
        let (lo, hi) = math::shr_i128($value.low(), $value.high(), $shift as u32);
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
            let max = u256::from_u16(256);
            let other = other.as_u256();
            debug_assert!(u256_lt(other, max), "attempt to shift left with overflow");
            let shift = (other.low() & (u32::MAX as u128)) as u32;
            shift_const_impl!(@shl self, shift)
        }

        /// Const evaluation of shr.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        pub const fn $shr(self, other: $t) -> Self {
            let max = u256::from_u16(256);
            let other = other.as_u256();
            debug_assert!(u256_lt(other, max), "attempt to shift left with overflow");
            let shift = (other.low() & (u32::MAX as u128)) as u32;
            shift_const_impl!(@shr self, shift)
        }
    );
}

// Const implementations for Shl
impl i256 {
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

impl Shl for i256 {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shl(self, other: Self) -> Self::Output {
        let shift = other.low() & (u32::MAX as u128);
        shift_const_impl!(@shl self, shift)
    }
}

ref_impl!(i256, Shl, shl, other: &i256);
ref_t_impl!(i256, Shl, shl);

impl Shr for i256 {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shr(self, other: Self) -> Self::Output {
        let shift = other.low() & (u32::MAX as u128);
        shift_const_impl!(@shr self, shift)
    }
}

ref_impl!(i256, Shr, shr, other: &i256);
ref_t_impl!(i256, Shr, shr);

macro_rules! shift_impl {
    (@mod $($t:ty)*) => ($(
        impl Shl<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                let shift = other % 256;
                shift_const_impl!(@shl self, shift)
            }
        }

        impl Shr<$t> for i256 {
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
        impl Shl<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            fn shl(self, other: $t) -> Self::Output {
                shift_const_impl!(@shl self, other)
            }
        }

        impl Shr<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            fn shr(self, other: $t) -> Self::Output {
                shift_const_impl!(@shr self, other)
            }
        }
    )*);

    (@256 $($t:ty)*) => ($(
        impl Shl<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                let shift = other % u256::from_u16(256);
                let shift = shift.as_u32();
                shift_const_impl!(@shl self, shift)
            }
        }

        impl Shr<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shr(self, other: $t) -> Self::Output {
                let shift = other % u256::from_u16(256);
                let shift = shift.as_u32();
                shift_const_impl!(@shr self, shift)
            }
        }
    )*);

    ($($t:ty)*) => ($(
        impl Shl<&$t> for i256 {
            type Output = <Self as Shl>::Output;

            #[inline(always)]
            fn shl(self, other: &$t) -> Self::Output {
                self.shl(*other)
            }
        }

        impl ShlAssign<$t> for i256 {
            #[inline(always)]
            fn shl_assign(&mut self, other: $t) {
                *self = self.shl(other);
            }
        }

        impl ShlAssign<&$t> for i256 {
            #[inline(always)]
            fn shl_assign(&mut self, other: &$t) {
                *self = self.shl(other);
            }
        }

        impl Shr<&$t> for i256 {
            type Output = <Self as Shr>::Output;

            #[inline(always)]
            fn shr(self, other: &$t) -> Self::Output {
                self.shr(*other)
            }
        }

        impl ShrAssign<$t> for i256 {
            #[inline(always)]
            fn shr_assign(&mut self, other: $t) {
                *self = self.shr(other);
            }
        }

        impl ShrAssign<&$t> for i256 {
            #[inline(always)]
            fn shr_assign(&mut self, other: &$t) {
                *self = self.shr(other);
            }
        }
    )*);
}

shift_impl! { @nomod i8 u8 }
shift_impl! { @mod i16 i32 i64 i128 isize u16 u32 u64 u128 usize }
shift_impl! { @256 u256 }
shift_impl! { i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 u256 usize }

impl Sub for i256 {
    type Output = i256;

    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_sub(rhs)
        } else {
            self.checked_sub(rhs).expect("attempt to subtract with overflow")
        }
    }
}

op_impl!(i256, Sub, SubAssign, sub, sub_assign);

impl TryFrom<u256> for i256 {
    type Error = TryFromIntError;

    #[inline(always)]
    fn try_from(u: u256) -> Result<Self, TryFromIntError> {
        if u < Self::MAX.as_u256() {
            Ok(Self::from_u256(u))
        } else {
            Err(TryFromIntError {})
        }
    }
}

impl fmt::UpperExp for i256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.is_negative() {
            write!(f, "-")?;
        } else if f.sign_plus() {
            write!(f, "+")?;
        }
        fmt::UpperExp::fmt(&self.abs().as_u256(), f)
    }
}

impl fmt::UpperHex for i256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: UpperHex for negative numbers uses wrapping formats.
        fmt::UpperHex::fmt(&self.as_u256(), f)
    }
}

/// Const implementation of `Neg` for internal algorithm use.
#[inline(always)]
const fn neg(x: i256) -> i256 {
    // NOTE: This is identical to `add(not(x), 1i256)`
    let (lo, hi) = math::neg_i128(x.low(), x.high());
    let actual = i256::new(lo, hi);
    let expected = i256::from_u8(0).wrapping_sub(x);
    debug_assert!(eq(actual, expected));
    actual
}

/// Const implementation of `BitAnd` for internal algorithm use.
#[inline(always)]
const fn bitand(lhs: i256, rhs: i256) -> i256 {
    i256::new(lhs.low() & rhs.low(), lhs.high() & rhs.high())
}

/// Const implementation of `BitOr` for internal algorithm use.
#[inline(always)]
const fn bitor(lhs: i256, rhs: i256) -> i256 {
    i256::new(lhs.low() | rhs.low(), lhs.high() | rhs.high())
}

/// Const implementation of `BitXor` for internal algorithm use.
#[inline(always)]
const fn bitxor(lhs: i256, rhs: i256) -> i256 {
    i256::new(lhs.low() ^ rhs.low(), lhs.high() ^ rhs.high())
}

/// Const implementation of `Not` for internal algorithm use.
#[inline(always)]
const fn not(n: i256) -> i256 {
    let (lo, hi) = math::not_i128(n.low(), n.high());
    i256::new(lo, hi)
}

/// Const implementation of `Eq` for internal algorithm use.
#[inline(always)]
const fn eq(lhs: i256, rhs: i256) -> bool {
    lhs.low() == rhs.low() && lhs.high() == rhs.high()
}

// NOTE: Because of two's complement, these comparisons are always normal.
/// Const implementation of `PartialOrd::lt` for internal algorithm use.
#[inline(always)]
pub(crate) const fn lt(lhs: i256, rhs: i256) -> bool {
    lhs.high() < rhs.high() || (lhs.high() == rhs.high() && lhs.low() < rhs.low())
}

/// Const implementation of `PartialOrd::le` for internal algorithm use.
#[inline(always)]
const fn le(lhs: i256, rhs: i256) -> bool {
    lhs.high() < rhs.high() || (lhs.high() == rhs.high() && lhs.low() <= rhs.low())
}

/// Const implementation of `PartialOrd::gt` for internal algorithm use.
#[inline(always)]
const fn gt(lhs: i256, rhs: i256) -> bool {
    lhs.high() > rhs.high() || (lhs.high() == rhs.high() && lhs.low() > rhs.low())
}

/// Const implementation of `PartialOrd::ge` for internal algorithm use.
#[inline(always)]
const fn ge(lhs: i256, rhs: i256) -> bool {
    lhs.high() > rhs.high() || (lhs.high() == rhs.high() && lhs.low() >= rhs.low())
}

/// Const implementation of `PartialOrd::cmp` for internal algorithm use.
#[inline(always)]
const fn cmp(lhs: i256, rhs: i256) -> Ordering {
    if lhs.high() < rhs.high() {
        Ordering::Less
    } else if lhs.high() > rhs.high() {
        Ordering::Greater
    } else if lhs.low() < rhs.low() {
        Ordering::Less
    } else if lhs.low() > rhs.low() {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

from_str_radix_impl!(i256, true);

#[cfg(test)]
mod tests {
    use super::*;

    #[inline(always)]
    fn parse(expected: i256, radix: u32, s: &str) {
        // check a full roundtrip
        let res: Result<i256, ParseIntError> = i256::from_str_radix(s, radix);
        assert!(res.is_ok());
        let actual = res.unwrap();
        assert_eq!(expected, actual);

        let as_str = actual.to_string();
        let res: Result<i256, ParseIntError> = i256::from_str_radix(&as_str, 10);
        assert!(res.is_ok());
        let actual = res.unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn from_str_radix_test() {
        let cases = [
            (
                i256::MIN,
                10,
                "-57896044618658097711785492504343953926634992332820282019728792003956564819968",
            ),
            (
                i256::MAX,
                10,
                "+57896044618658097711785492504343953926634992332820282019728792003956564819967",
            ),
            (0xffffffffffffffffi128.into(), 16, "+ffffffffffffffff"),
            (0x123456789ab123i128.into(), 10, "5124095576027427"),
            (0x123456789ab123i128.into(), 16, "+123456789ab123"),
            ((-15i128).into(), 10, "-15"),
            ((-255i128).into(), 16, "-FF"),
            (255i128.into(), 16, "+FF"),
        ];
        for case in cases {
            parse(case.0, case.1, case.2);
        }

        let failing = [
            (16, "-0xFF"),
            (16, "+0xFF"),
            (16, "0xFF"),
            (10, "FF"),
            (10, "a9"),
            (10, "12.34"),
            (10, "1234_67"),
            (10, "57896044618658097711785492504343953926634992332820282019728792003956564819968"),
            (10, "115792089237316195423570985008687907853269984665640564039457584007913129639935"),
            (10, "115792089237316195423570985008687907853269984665640564039457584007913129639936"),
            (16, "+ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
        ];
        for case in failing {
            let res: Result<i256, ParseIntError> = i256::from_str_radix(case.1, case.0);
            assert!(res.is_err());
        }
    }

    #[test]
    #[should_panic]
    fn from_str_radix_neg_test() {
        _ = i256::from_str_radix("-1F", 10).unwrap();
    }
}
