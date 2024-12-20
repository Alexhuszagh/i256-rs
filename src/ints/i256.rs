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
//! `checked_*`, `overflowing_*` and `*_small` variants are
//! likely based on the core implementations.

use core::cmp::Ordering;
use core::ops::*;
use core::str::FromStr;
use core::{fmt, mem};

use crate::error::{IntErrorKind, ParseIntError, TryFromIntError};
use crate::ints::u256::lt as u256_lt;
use crate::math;
use crate::numtypes::*;
use crate::u256;

// FIXME: Add support for [Saturating][core::num::Saturating] and
// [Wrapping][core::num::Wrapping] when we drop support for <1.74.0.

/// The 256-bit signed integer type.
///
/// The high and low words depend on the target endianness.
/// Conversion to and from big endian should be done via
/// [`to_le_bytes`] and [`to_be_bytes`]. or using
/// [`get_high`] and [`get_low`]. This is stored
/// as if it were a native, signed integer, as
/// two's complement.
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
pub struct i256 {
    pub(crate) lo: u128,
    pub(crate) hi: i128,
}

/// The 256-bit signed integer type.
///
/// The high and low words depend on the target endianness.
/// Conversion to and from big endian should be done via
/// [`to_le_bytes`] and [`to_be_bytes`]. or using
/// [`get_high`] and [`get_low`]. This is stored
/// as if it were a native, signed integer, as
/// two's complement.
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
pub struct i256 {
    pub(crate) hi: i128,
    pub(crate) lo: u128,
}

impl i256 {
    /// The smallest value that can be represented by this integer type.
    pub const MIN: Self = Self::new(0, 0);

    /// The largest value that can be represented by this integer type
    /// (2<sup>256</sup> - 1).
    pub const MAX: Self = Self::new(u128::MAX, i128::MAX);

    /// The size of this integer type in bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use i256::i256;
    /// assert_eq!(i256::BITS, 256);
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
    /// # use i256::i256;
    /// let n = i256::MAX >> 2i32;
    /// assert_eq!(n.leading_zeros(), 3);
    ///
    /// let zero = i256::MIN;
    /// assert_eq!(zero.leading_zeros(), 256);
    ///
    /// let max = i256::MAX;
    /// assert_eq!(max.leading_zeros(), 1);
    /// ```
    #[inline(always)]
    pub const fn leading_zeros(self) -> u32 {
        let mut leading = (self.hi as u128).leading_zeros();
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
        let (lo, hi) = math::rotate_left_i128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Shifts the bits to the right by a specified amount, `n`,
    /// wrapping the truncated bits to the beginning of the resulting
    /// integer.
    ///
    /// Please note this isn't the same operation as the `>>` shifting operator!
    #[inline(always)]
    pub const fn rotate_right(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_right_i128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Reverses the byte order of the integer.
    #[inline(always)]
    pub const fn swap_bytes(self) -> Self {
        let (lo, hi) = math::swap_bytes_i128(self.lo, self.hi);
        Self::new(lo, hi)
    }

    /// Reverses the order of bits in the integer. The least significant
    /// bit becomes the most significant bit, second least-significant bit
    /// becomes second most-significant bit, etc.
    #[inline(always)]
    pub const fn reverse_bits(self) -> Self {
        let (lo, hi) = math::reverse_bits_i128(self.lo, self.hi);
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

    /// Checked addition with an unsigned integer. Computes `self + rhs`,
    /// returning `None` if overflow occurred.
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
    #[inline(always)]
    pub fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
        if self.is_div_none(rhs) {
            None
        } else {
            Some(self.div_euclid(rhs))
        }
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None` if
    /// `rhs == 0` or the division results in overflow.
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
    #[inline(always)]
    pub fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
        if self.is_div_none(rhs) {
            None
        } else {
            Some(self.wrapping_rem_euclid(rhs))
        }
    }

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
    #[inline(always)]
    pub const fn checked_abs(self) -> Option<Self> {
        if self.is_negative() {
            self.checked_neg()
        } else {
            Some(self)
        }
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if
    /// overflow occurred.
    #[inline]
    pub const fn checked_pow(self, exp: u32) -> Option<Self> {
        match self.overflowing_pow(exp) {
            (value, true) => Some(value),
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
    #[inline(always)]
    pub const fn saturating_add(self, rhs: Self) -> Self {
        if self.is_negative() {
            self.saturating_sub_unsigned(rhs.wrapping_abs().as_u256())
        } else {
            self.saturating_add_unsigned(rhs.as_u256())
        }
    }

    /// Saturating addition with an unsigned integer. Computes `self + rhs`,
    /// saturating at the numeric bounds instead of overflowing.
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
    #[inline(always)]
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        if self.is_negative() {
            self.saturating_add_unsigned(rhs.wrapping_abs().as_u256())
        } else {
            self.saturating_sub_unsigned(rhs.as_u256())
        }
    }

    /// Saturating subtraction with an unsigned integer. Computes `self - rhs`,
    /// saturating at the numeric bounds instead of overflowing.
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
    #[inline(always)]
    pub const fn saturating_neg(self) -> Self {
        Self::from_u8(0).saturating_sub(self)
    }

    /// Saturating absolute value. Computes `self.abs()`, returning `MAX` if
    /// `self == MIN` instead of overflowing.
    #[inline(always)]
    pub const fn saturating_abs(self) -> Self {
        if self.is_negative() {
            self.saturating_neg()
        } else {
            self
        }
    }

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at
    /// the numeric bounds instead of overflowing.
    #[inline(always)]
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
    #[inline(always)]
    pub fn saturating_div(self, rhs: Self) -> Self {
        match self.overflowing_div(rhs) {
            (result, false) => result,
            (_result, true) => Self::MAX, // MIN / -1 is the only possible saturating overflow
        }
    }

    /// Saturating integer exponentiation. Computes `self.pow(exp)`,
    /// saturating at the numeric bounds instead of overflowing.
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
    #[inline(always)]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        let (lo, hi, _) = math::add_i128(self.lo, self.hi, rhs.lo, rhs.hi);
        i256::new(lo, hi)
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around
    /// at the boundary of the type.
    #[inline(always)]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        let (lo, hi, _) = math::sub_i128(self.lo, self.hi, rhs.lo, rhs.hi);
        i256::new(lo, hi)
    }

    /// Wrapping (modular) subtraction with an unsigned integer. Computes
    /// `self - rhs`, wrapping around at the boundary of the type.
    #[inline(always)]
    pub const fn wrapping_sub_unsigned(self, rhs: u256) -> Self {
        self.wrapping_sub(Self::from_u256(rhs))
    }

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping
    /// around at the boundary of the type.
    #[inline(always)]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        let (lo, hi) = math::mul_i128(self.lo, self.hi, rhs.lo, rhs.hi);
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
    #[inline(always)]
    pub fn wrapping_div(self, rhs: Self) -> Self {
        div_rem(self, rhs).0
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
    #[inline(always)]
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
    #[inline(always)]
    pub fn wrapping_rem(self, rhs: Self) -> Self {
        div_rem(self, rhs).1
    }

    /// Wrapping Euclidean remainder. Computes `self.rem_euclid(rhs)`, wrapping
    /// around at the boundary of the type.
    ///
    /// Wrapping will only occur in `MIN % -1` on a signed type (where `MIN` is
    /// the negative minimal value for the type). In this case, this method
    /// returns 0.
    #[inline(always)]
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
    #[inline(always)]
    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        let (lo, hi) = math::shl_i128(self.lo, self.hi, rhs % 256);
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
    #[inline(always)]
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        let (lo, hi) = math::shr_i128(self.lo, self.hi, rhs % 256);
        Self::new(lo, hi)
    }

    /// Wrapping (modular) absolute value. Computes `self.abs()`, wrapping
    /// around at the boundary of the type.
    ///
    /// The only case where such wrapping can occur is when one takes the
    /// absolute value of the negative minimal value for the type; this is a
    /// positive value that is too large to represent in the type. In such a
    /// case, this function returns `MIN` itself.
    #[inline(always)]
    pub const fn wrapping_abs(self) -> Self {
        if self.is_negative() {
            self.wrapping_neg()
        } else {
            self
        }
    }

    /// Computes the absolute value of `self` without any wrapping
    /// or panicking.
    #[inline(always)]
    pub const fn unsigned_abs(self) -> u256 {
        self.wrapping_abs().as_u256()
    }

    /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`,
    /// wrapping around at the boundary of the type.
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
    #[inline(always)]
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) = math::add_i128(self.lo, self.hi, rhs.lo, rhs.hi);
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates `self` + `rhs` with an unsigned `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
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
    #[inline(always)]
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) = math::sub_i128(self.lo, self.hi, rhs.lo, rhs.hi);
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates `self` - `rhs` with an unsigned `rhs`.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
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
    #[inline(always)]
    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_i128(self.lo, self.hi, rhs.lo, rhs.hi);
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
    #[inline(always)]
    pub fn overflowing_div(self, rhs: Self) -> (Self, bool) {
        if eq(self, Self::MIN) & eq(rhs, Self::from_i8(-1)) {
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
    #[inline(always)]
    pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
        (self.wrapping_shr(rhs), rhs >= Self::BITS)
    }

    /// Computes the absolute value of `self`.
    ///
    /// Returns a tuple of the absolute version of self along with a boolean
    /// indicating whether an overflow happened.
    #[inline(always)]
    pub const fn overflowing_abs(self) -> (Self, bool) {
        (self.wrapping_abs(), eq(self, Self::MIN))
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
    #[inline(always)]
    pub fn div_euclid(self, rhs: Self) -> Self {
        if cfg!(not(debug_assertions)) {
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
    #[inline(always)]
    pub fn rem_euclid(self, rhs: Self) -> Self {
        if cfg!(not(debug_assertions)) {
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
    #[inline(always)]
    pub fn div_floor(self, rhs: Self) -> Self {
        let (d, r) = div_rem(self, rhs);

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
    #[inline(always)]
    pub fn div_ceil(self, rhs: Self) -> Self {
        let (d, r) = div_rem(self, rhs);

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
    #[inline(always)]
    pub const fn abs(self) -> Self {
        if self.is_negative() {
            self.wrapping_neg()
        } else {
            self
        }
    }

    /// Computes the absolute difference between `self` and `other`.
    ///
    /// This function always returns the correct answer without overflow or
    /// panics by returning an unsigned integer.
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
    #[inline(always)]
    pub const fn is_positive(self) -> bool {
        // NOTE: Because this is 2's complement, we can optimize like this.
        self.hi > 0 || (self.hi == 0 && self.lo > 0)
    }

    /// Returns `true` if `self` is negative and `false` if the number is zero
    /// or positive.
    #[inline(always)]
    pub const fn is_negative(self) -> bool {
        // NOTE: Because this is 2's complement, we can optimize like this.
        self.hi < 0
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
    #[inline]
    pub const fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        if radix < 2 || radix > 36 {
            panic!("from_str_radix_int: must lie in the range `[2, 36]`");
        }
        todo!();
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
        Self {
            lo,
            hi,
        }
    }

    /// Get the high 128 bits of the signed integer.
    #[inline(always)]
    pub const fn get_high(self) -> i128 {
        self.hi
    }

    /// Get the low 128 bits of the signed integer.
    #[inline(always)]
    pub const fn get_low(self) -> u128 {
        self.lo
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
        math::as_unarrow_i128(self.lo, self.hi)
    }

    /// Convert the 256-bit signed integer to an `u256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u256(&self) -> u256 {
        let (lo, hi) = math::wide_cast_i128(self.lo, self.hi);
        u256::new(lo, hi)
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
        math::as_inarrow_i128(self.lo, self.hi)
    }

    /// Convert the 256-bit signed integer to an `i256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i256(&self) -> i256 {
        *self
    }

    /// Add the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub fn add_usmall(self, n: u128) -> Self {
        if cfg!(not(debug_assertions)) {
            self.wrapping_add_usmall(n)
        } else {
            self.checked_add_usmall(n).expect("attempt to add with overflow")
        }
    }

    /// Add the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub fn wrapping_add_usmall(self, n: u128) -> Self {
        let (lo, hi, _) = math::add_usmall_i128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Add the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn overflowing_add_usmall(self, n: u128) -> (Self, bool) {
        let (lo, hi, overflowed) = math::add_usmall_i128(self.lo, self.hi, n);
        (Self::new(lo, hi), overflowed)
    }

    /// Add the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn checked_add_usmall(self, n: u128) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add_usmall(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Add the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub fn add_ismall(self, n: i128) -> Self {
        if cfg!(not(debug_assertions)) {
            self.wrapping_add_ismall(n)
        } else {
            self.checked_add_ismall(n).expect("attempt to add with overflow")
        }
    }

    /// Add the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub fn wrapping_add_ismall(self, n: i128) -> Self {
        let (lo, hi, _) = math::add_ismall_i128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Add the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn overflowing_add_ismall(self, n: i128) -> (Self, bool) {
        let (lo, hi, overflowed) = math::add_ismall_i128(self.lo, self.hi, n);
        (Self::new(lo, hi), overflowed)
    }

    /// Add the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn checked_add_ismall(self, n: i128) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add_ismall(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Subtract the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub fn sub_usmall(self, n: u128) -> Self {
        if cfg!(not(debug_assertions)) {
            self.wrapping_sub_usmall(n)
        } else {
            self.checked_sub_usmall(n).expect("attempt to subtract with overflow")
        }
    }

    /// Subtract the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub fn wrapping_sub_usmall(self, n: u128) -> Self {
        let (lo, hi, _) = math::sub_usmall_i128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Subtract the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn overflowing_sub_usmall(self, n: u128) -> (Self, bool) {
        let (lo, hi, overflowed) = math::sub_usmall_i128(self.lo, self.hi, n);
        (Self::new(lo, hi), overflowed)
    }

    /// Subtract the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn checked_sub_usmall(self, n: u128) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub_usmall(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Subtract the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub fn sub_ismall(self, n: i128) -> Self {
        if cfg!(not(debug_assertions)) {
            self.wrapping_sub_ismall(n)
        } else {
            self.checked_sub_ismall(n).expect("attempt to subtract with overflow")
        }
    }

    /// Subtract the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub fn wrapping_sub_ismall(self, n: i128) -> Self {
        let (lo, hi, _) = math::sub_ismall_i128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Subtract the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn overflowing_sub_ismall(self, n: i128) -> (Self, bool) {
        let (lo, hi, overflowed) = math::sub_ismall_i128(self.lo, self.hi, n);
        (Self::new(lo, hi), overflowed)
    }

    /// Subtract the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn checked_sub_ismall(self, n: i128) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub_ismall(n);
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
    pub fn mul_usmall(self, n: u128) -> Self {
        if cfg!(not(debug_assertions)) {
            self.wrapping_mul_usmall(n)
        } else {
            self.checked_mul_usmall(n).expect("attempt to multiply with overflow")
        }
    }

    /// Multiply the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub fn wrapping_mul_usmall(self, n: u128) -> Self {
        let (lo, hi) = math::mul_usmall_i128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_usmall(self, n: u128) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_usmall_i128(self.lo, self.hi, n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a small, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn checked_mul_usmall(self, n: u128) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul_usmall(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Multiply the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub fn mul_ismall(self, n: i128) -> Self {
        if cfg!(not(debug_assertions)) {
            self.wrapping_mul_ismall(n)
        } else {
            self.checked_mul_ismall(n).expect("attempt to multiply with overflow")
        }
    }

    /// Multiply the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub fn wrapping_mul_ismall(self, n: i128) -> Self {
        let (lo, hi) = math::mul_ismall_i128(self.lo, self.hi, n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_ismall(self, n: i128) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_ismall_i128(self.lo, self.hi, n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a small, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn checked_mul_ismall(self, n: i128) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul_ismall(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn div_rem_usmall(self, n: u64) -> (Self, u64) {
        if cfg!(not(debug_assertions)) {
            self.wrapping_div_rem_usmall(n)
        } else {
            self.checked_div_rem_usmall(n).expect("attempt to divide by zero")
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do. This always
    /// wraps, which can never happen in practice.
    #[inline(always)]
    pub fn wrapping_div_rem_usmall(self, n: u64) -> (Self, u64) {
        // SAFETY: Safe since these are plain old data.
        unsafe {
            let x: [u64; 4] = mem::transmute(self.wrapping_abs().as_u256().to_le_bytes());
            let (div, rem) = math::div_rem_small(&x, n);
            let div = u256::from_le_bytes(mem::transmute::<[u64; 4], [u8; 32]>(div)).as_i256();
            // rem is always positive: `-65 % 64` is 63
            (div, rem)
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_rem_usmall(self, n: u64) -> Option<(Self, u64)> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_rem_usmall(n))
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_rem_usmall(self, n: u64) -> ((Self, u64), bool) {
        (self.wrapping_div_rem_usmall(n), false)
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn div_rem_ismall(self, n: i64) -> (Self, i64) {
        if cfg!(not(debug_assertions)) {
            self.wrapping_div_rem_ismall(n)
        } else {
            self.checked_div_rem_ismall(n).expect("attempt to divide by zero")
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do. This always
    /// wraps, which can never happen in practice.
    #[inline(always)]
    pub fn wrapping_div_rem_ismall(self, n: i64) -> (Self, i64) {
        // SAFETY: Safe since these are plain old data.
        unsafe {
            let x: [u64; 4] = mem::transmute(self.wrapping_abs().as_u256().to_le_bytes());
            let (div, rem) = math::div_rem_small(&x, n.wrapping_abs() as u64);
            let mut div = u256::from_le_bytes(mem::transmute::<[u64; 4], [u8; 32]>(div)).as_i256();
            let mut rem = rem as i64;

            // convert to our correct signs, get the product
            if self.is_negative() != n.is_negative() {
                div = div.wrapping_neg();
            }
            if self.is_negative() {
                rem = rem.wrapping_neg();
            }

            (div, rem)
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_rem_ismall(self, n: i64) -> Option<(Self, i64)> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_rem_ismall(n))
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_rem_ismall(self, n: i64) -> ((Self, i64), bool) {
        (self.wrapping_div_rem_ismall(n), false)
    }

    /// Div the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn div_usmall(self, n: u64) -> Self {
        if cfg!(not(debug_assertions)) {
            self.wrapping_div_usmall(n)
        } else {
            self.checked_div_usmall(n).expect("attempt to divide by zero")
        }
    }

    /// Div the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_div_usmall(self, n: u64) -> Self {
        self.wrapping_div_rem_usmall(n).0
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_usmall(self, n: u64) -> Option<Self> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_usmall(n))
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_usmall(self, n: u64) -> (Self, bool) {
        if n == 0 {
            (Self::MAX, true)
        } else {
            (self.wrapping_div_usmall(n), false)
        }
    }

    /// Div the 256-bit integer by a small, 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn div_ismall(self, n: i64) -> Self {
        if cfg!(not(debug_assertions)) {
            self.div_rem_ismall(n).0
        } else {
            self.checked_div_ismall(n).expect("attempt to divide by zero")
        }
    }

    /// Div the 256-bit integer by a small, 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_div_ismall(self, n: i64) -> Self {
        self.wrapping_div_rem_ismall(n).0
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit signed factor.
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_ismall(self, n: i64) -> Option<Self> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_ismall(n))
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_ismall(self, n: i64) -> (Self, bool) {
        if n == 0 {
            (Self::MAX, true)
        } else {
            (self.wrapping_div_ismall(n), false)
        }
    }

    /// Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn rem_usmall(self, n: u64) -> u64 {
        if cfg!(not(debug_assertions)) {
            self.wrapping_rem_usmall(n)
        } else {
            self.checked_rem_usmall(n).expect("attempt to divide by zero")
        }
    }

    /// Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_rem_usmall(self, n: u64) -> u64 {
        self.wrapping_div_rem_usmall(n).1
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_rem_usmall(self, n: u64) -> Option<u64> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_rem_usmall(n))
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_rem_usmall(self, n: u64) -> (u64, bool) {
        if n == 0 {
            (0, true)
        } else {
            (self.wrapping_rem_usmall(n), false)
        }
    }

    /// Rem the 256-bit integer by a small, 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn rem_ismall(self, n: i64) -> i64 {
        if cfg!(not(debug_assertions)) {
            self.wrapping_rem_ismall(n)
        } else {
            self.checked_rem_ismall(n).expect("attempt to divide by zero")
        }
    }

    /// Rem the 256-bit integer by a small, 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_rem_ismall(self, n: i64) -> i64 {
        self.wrapping_div_rem_ismall(n).1
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit signed factor.
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_rem_ismall(self, n: i64) -> Option<i64> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_rem_ismall(n))
        }
    }

    /// Div/Rem the 256-bit integer by a small, 64-bit signed factor.
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_rem_ismall(self, n: i64) -> (i64, bool) {
        if n == 0 {
            (0, true)
        } else {
            (self.wrapping_rem_ismall(n), false)
        }
    }
}

impl Add for i256 {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        if cfg!(not(debug_assertions)) {
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
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.is_negative() {
            write!(f, "-")?;
        } else if f.sign_plus() {
            write!(f, "+")?;
        }
        fmt::Display::fmt(&self.abs().as_u256(), f)
    }
}

impl Div for i256 {
    type Output = Self;

    #[inline(always)]
    fn div(self, rhs: Self) -> Self::Output {
        if cfg!(not(debug_assertions)) {
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
    /// the lexical implementation.
    #[inline(always)]
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
    #[inline(always)]
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
        if cfg!(not(debug_assertions)) {
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
        if cfg!(not(debug_assertions)) {
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
        let (lo, hi) = math::shl_i128($value.lo, $value.hi, $shift as u32);
        Self::new(lo, hi)
    }};

    (@shr $value:ident, $shift:ident) => {{
        let (lo, hi) = math::shr_i128($value.lo, $value.hi, $shift as u32);
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
            let shift = (other.lo & (u32::MAX as u128)) as u32;
            shift_const_impl!(@shl self, shift)
        }

        /// Const evaluation of shr.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        pub const fn $shr(self, other: $t) -> Self {
            let max = u256::from_u16(256);
            let other = other.as_u256();
            debug_assert!(u256_lt(other, max), "attempt to shift left with overflow");
            let shift = (other.lo & (u32::MAX as u128)) as u32;
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
        let shift = other.lo & (u32::MAX as u128);
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
        let shift = other.lo & (u32::MAX as u128);
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
        if cfg!(not(debug_assertions)) {
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

// NOTE: Our algorithm assumes little-endian order, which we might not have.
// So, we transmute to LE order prior to the call.
/// Large division/remainder calculation. This will panic if `rhs == 0` or if
/// `rhs == -1 && lhs == i256::MIN`.
#[inline]
fn div_rem(lhs: i256, rhs: i256) -> (i256, i256) {
    // SAFETY: Safe since these are plain old data.
    unsafe {
        // Do division as positive numbers, and if `lhs.is_sign_negative() ^
        // rhs.is_sign_negative()`, then we can inver the sign
        let x: [u64; 4] = mem::transmute(lhs.wrapping_abs().as_u256().to_le_bytes());
        let y: [u64; 4] = mem::transmute(rhs.wrapping_abs().as_u256().to_le_bytes());

        // get our unsigned division product
        let (div, rem) = math::div_rem_big(&x, &y);
        let mut div = u256::from_le_bytes(mem::transmute::<[u64; 4], [u8; 32]>(div)).as_i256();
        let mut rem = u256::from_le_bytes(mem::transmute::<[u64; 4], [u8; 32]>(rem)).as_i256();

        // convert to our correct signs, get the product
        if lhs.is_negative() != rhs.is_negative() {
            div = div.wrapping_neg();
        }
        if lhs.is_negative() {
            rem = rem.wrapping_neg();
        }

        (div, rem)
    }
}

/// Const implementation of `Neg` for internal algorithm use.
#[inline(always)]
const fn neg(x: i256) -> i256 {
    // NOTE: This is identical to `add(not(x), 1i256)`
    let twos_neg = not(x).wrapping_add(i256::from_u8(1));
    debug_assert!(eq(i256::from_u8(0).wrapping_sub(x), twos_neg));
    i256::from_u8(0).wrapping_sub(x)
}

/// Const implementation of `BitAnd` for internal algorithm use.
#[inline(always)]
const fn bitand(lhs: i256, rhs: i256) -> i256 {
    i256::new(lhs.lo & rhs.lo, lhs.hi & rhs.hi)
}

/// Const implementation of `BitOr` for internal algorithm use.
#[inline(always)]
const fn bitor(lhs: i256, rhs: i256) -> i256 {
    i256::new(lhs.lo | rhs.lo, lhs.hi | rhs.hi)
}

/// Const implementation of `BitXor` for internal algorithm use.
#[inline(always)]
const fn bitxor(lhs: i256, rhs: i256) -> i256 {
    i256::new(lhs.lo ^ rhs.lo, lhs.hi ^ rhs.hi)
}

/// Const implementation of `Not` for internal algorithm use.
#[inline(always)]
const fn not(n: i256) -> i256 {
    i256::new(!n.lo, !n.hi)
}

/// Const implementation of `Eq` for internal algorithm use.
#[inline(always)]
const fn eq(lhs: i256, rhs: i256) -> bool {
    lhs.lo == rhs.lo && lhs.hi == rhs.hi
}

// NOTE: Because of two's complement, these comparisons are always normal.
/// Const implementation of `PartialOrd::lt` for internal algorithm use.
#[inline(always)]
const fn lt(lhs: i256, rhs: i256) -> bool {
    lhs.hi < rhs.hi || (lhs.hi == rhs.hi && lhs.lo < rhs.lo)
}

/// Const implementation of `PartialOrd::le` for internal algorithm use.
#[inline(always)]
const fn le(lhs: i256, rhs: i256) -> bool {
    lhs.hi < rhs.hi || (lhs.hi == rhs.hi && lhs.lo <= rhs.lo)
}

/// Const implementation of `PartialOrd::gt` for internal algorithm use.
#[inline(always)]
const fn gt(lhs: i256, rhs: i256) -> bool {
    lhs.hi > rhs.hi || (lhs.hi == rhs.hi && lhs.lo > rhs.lo)
}

/// Const implementation of `PartialOrd::ge` for internal algorithm use.
#[inline(always)]
const fn ge(lhs: i256, rhs: i256) -> bool {
    lhs.hi > rhs.hi || (lhs.hi == rhs.hi && lhs.lo >= rhs.lo)
}

/// Const implementation of `PartialOrd::cmp` for internal algorithm use.
#[inline(always)]
const fn cmp(lhs: i256, rhs: i256) -> Ordering {
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
