//! Defines high-level operations, which respect overflow checks.

#[rustfmt::skip]
macro_rules! define {
    (
        signed_type => $s_t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        #[inline(always)]
        const fn is_div_overflow(self, rhs: Self) -> bool {
            _ = rhs;
            false
        }

        // If the checked methods should return `None`.
        #[inline(always)]
        const fn is_div_none(self, rhs: Self) -> bool {
            rhs.eq_const(Self::from_u8(0))
        }

        $crate::shared::ops::define!(
            type => $s_t,
            wide_type => $wide_t,
            see_type => $see_t,
        );

        /// Performs Euclidean division.
        ///
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self / rhs`.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, div_euclid)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_euclid(self, rhs: Self) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_euclid(rhs)
            } else {
                match self.checked_div_euclid(rhs) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Calculates the least remainder of `self (mod rhs)`.
        ///
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self % rhs`.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, rem_euclid)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_euclid(self, rhs: Self) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_rem(rhs)
            } else {
                match self.checked_rem_euclid(rhs) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Calculates the quotient of `self` and `rhs`, rounding the result towards
        /// negative infinity.
        ///
        /// This is the same as performing `self / rhs` for all unsigned integers.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, div_floor)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_floor(self, rhs: Self) -> Self {
            self.wrapping_div(rhs)
        }

        /// Calculates the quotient of `self` and `rhs`, rounding the result towards
        /// positive infinity.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, div_ceil)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_ceil(self, rhs: Self) -> Self {
            let (d, r) = self.wrapping_div_rem(rhs);
            if !r.eq_const(Self::from_u8(0)) {
                // NOTE: This can't overflow
                d.wrapping_add_ulimb(1)
            } else {
                d
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
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, ilog)]
        #[inline(always)]
        pub fn ilog(self, base: Self) -> u32 {
            if let Some(log) = self.checked_ilog(base) {
                log
            } else {
                core::panic!("argument of integer logarithm must be positive")
            }
        }

        /// Returns the base 2 logarithm of the number, rounded down.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!(self)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, ilog2)]
        #[inline(always)]
        pub const fn ilog2(self) -> u32 {
            if let Some(log) = self.checked_ilog2() {
                log
            } else {
                core::panic!("argument of integer logarithm must be positive")
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
        //         core::panic!("argument of integer logarithm must be positive")
        //     }
        // }

        // FIXME: Stabilize when our MSRV goes to `1.84.0+`.
        // /// Returns the square root of the number, rounded down.
        // #[inline]
        // pub const fn isqrt(self) -> Self {
        //     todo!();
        // }

        /// Computes the absolute difference between `self` and `other`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, abs_diff)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn abs_diff(self, other: Self) -> Self {
            if self.lt_const(other) {
                other.wrapping_sub(self)
            } else {
                self.wrapping_sub(other)
            }
        }

        /// Calculates the smallest value greater than or equal to `self` that
        /// is a multiple of `rhs`.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::overflow_assertions_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u64, next_multiple_of)]
        #[inline]
        pub fn next_multiple_of(self, rhs: Self) -> Self {
            use core::ops::{Add, Rem, Sub};

            match self.rem(rhs) {
                Self::MIN => self,
                r => self.add(rhs.sub(r)),
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
                Self::MIN => self.eq_const(Self::MIN),
                _ => self.wrapping_rem(rhs).eq_const(Self::MIN),
            }
        }

        /// Returns `true` if and only if `self == 2^k` for some `k`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u64, is_power_of_two)]
        #[inline(always)]
        pub const fn is_power_of_two(self) -> bool {
            self.count_ones() == 1
        }

        #[inline]
        const fn one_less_than_next_power_of_two(self) -> Self {
            if self.le_const(Self::from_u8(1)) {
                return Self::MIN;
            }
            let p = self.wrapping_sub(Self::from_u8(1));
            let z = p.leading_zeros();
            Self::MAX.wrapping_shr(z)
        }

        /// Returns the smallest power of two greater than or equal to `self`.
        ///
        /// When return value overflows (i.e., `self > (1 << (N-1))` for type
        /// `uN`), it panics in debug mode and the return value is wrapped to 0 in
        /// release mode (the only situation in which this method can return 0).
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u64, next_power_of_two)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn next_power_of_two(self) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_next_power_of_two()
            } else {
                match self.checked_next_power_of_two() {
                    Some(v) => v,
                    None => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Calculates the middle point of `self` and `rhs`.
        ///
        /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a
        /// sufficiently-large unsigned integral type. This implies that the result
        /// is always rounded towards zero and that no overflow will ever occur.
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u64, midpoint)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn midpoint(self, rhs: Self) -> Self {
            // Use the well known branchless algorithm from Hacker's Delight to compute
            // `(a + b) / 2` without overflowing: `((a ^ b) >> 1) + (a & b)`.
            let xor = self.bitxor_const(rhs);
            xor.wrapping_shr(1).wrapping_add(self.bitand_const(rhs))
        }

        /// Calculates the complete product `self * rhs` without the possibility to overflow.
        ///
        /// This returns the low-order (wrapping) bits and the high-order (overflow) bits
        /// of the result as two separate values, in that order.
        ///
        /// If you also need to add a carry to the wide result, then you want
        /// [`Self::carrying_mul`] instead.
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// Please note that this example is shared between integer types.
        /// Which explains why `u32` is used here.
        ///
        /// ```rust,ignore
        /// #![feature(bigint_helper_methods)]
        /// assert_eq!(5u32.widening_mul(2), (10, 0));
        /// assert_eq!(1_000_000_000u32.widening_mul(10), (1410065408, 2));
        /// ```
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u64, widening_mul)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn widening_mul(self, rhs: Self) -> (Self, Self) {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();
            let (lo, hi) = $crate::math::mul::widening(&lhs, &rhs);
            (Self::from_ne_limbs(lo), Self::from_ne_limbs(hi))
        }

        /// Calculates the "full multiplication" `self * rhs + carry`
        /// without the possibility to overflow.
        ///
        /// This returns the low-order (wrapping) bits and the high-order (overflow) bits
        /// of the result as two separate values, in that order.
        ///
        /// Performs "long multiplication" which takes in an extra amount to add, and may return an
        /// additional amount of overflow. This allows for chaining together multiple
        /// multiplications to create "big integers" which represent larger values.
        ///
        /// If you don't need the `carry`, then you can use [`Self::widening_mul`] instead.
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u64, carrying_mul)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn carrying_mul(self, rhs: Self, carry: Self) -> (Self, Self) {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();
            let (lo, hi) = $crate::math::mul::widening(&lhs, &rhs);
            let (lo, overflowed) = Self::from_ne_limbs(lo).overflowing_add(carry);
            let hi = Self::from_ne_limbs(hi).add_ulimb(overflowed as $crate::ULimb);

            (lo, hi)
        }

        /// Calculates the "full multiplication" `self * rhs + carry + add`
        /// without the possibility to overflow.
        ///
        /// This returns the low-order (wrapping) bits and the high-order (overflow) bits
        /// of the result as two separate values, in that order.
        ///
        /// Performs "long multiplication" which takes in an extra amount to add, and may return an
        /// additional amount of overflow. This allows for chaining together multiple
        /// multiplications to create "big integers" which represent larger values.
        ///
        /// If you don't need the `add`, then you can use [`Self::carrying_mul`] instead.
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u64, carrying_mul_add)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn carrying_mul_add(self, rhs: Self, carry: Self, add: Self) -> (Self, Self) {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();
            let (lo, hi) = $crate::math::mul::widening(&lhs, &rhs);
            let (lo, overflowed1) = Self::from_ne_limbs(lo).overflowing_add(carry);
            let (lo, overflowed2) = lo.overflowing_add(add);
            let overflowed = (overflowed1 as $crate::ULimb) + (overflowed2 as $crate::ULimb);
            let hi = Self::from_ne_limbs(hi).add_ulimb(overflowed);

            (lo, hi)
        }
    };
}

pub(crate) use define;
