//! Operations for our limb operations on big integers.

macro_rules! define {
    () => {
        // LIMB

        /// Add [`ULimb`][crate::ULimb] to the big integer.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn add_ulimb(self, n: $crate::ULimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_add_ulimb(n)
            } else {
                match self.checked_add_ulimb(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Subtract [`ULimb`][crate::ULimb] from the big integer.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn sub_ulimb(self, n: $crate::ULimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_sub_ulimb(n)
            } else {
                match self.checked_sub_ulimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to subtract with overflow"),
                }
            }
        }

        /// Multiply our big integer by [`ULimb`][crate::ULimb].
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn mul_ulimb(self, n: $crate::ULimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_ulimb(n)
            } else {
                match self.checked_mul_ulimb(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to multiply with overflow"),
                }
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`ULimb`][crate::ULimb].
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_rem_ulimb(self, n: $crate::ULimb) -> (Self, $crate::ULimb) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_ulimb(n)
            } else {
                match self.checked_div_rem_ulimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Get the quotient of our big integer divided by [`ULimb`][crate::ULimb].
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_ulimb(self, n: $crate::ULimb) -> Self {
            self.div_rem_ulimb(n).0
        }

        /// Get the remainder of our big integer divided by [`ULimb`][crate::ULimb].
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_ulimb(self, n: $crate::ULimb) -> $crate::ULimb {
            self.div_rem_ulimb(n).1
        }

        // WIDE

        /// Add [`UWide`][crate::UWide] to the big integer.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn add_uwide(self, n: $crate::UWide) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_add_uwide(n)
            } else {
                match self.checked_add_uwide(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Subtract [`UWide`][crate::UWide] from the big integer.
        ///
        #[doc = $crate::shared::docs::wide_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn sub_uwide(self, n: $crate::UWide) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_sub_uwide(n)
            } else {
                match self.checked_sub_uwide(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to subtract with overflow"),
                }
            }
        }

        /// Multiply our big integer by [`UWide`][crate::UWide].
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn mul_uwide(self, n: $crate::UWide) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_uwide(n)
            } else {
                match self.checked_mul_uwide(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to multiply with overflow"),
                }
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`UWide`][crate::UWide].
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_rem_uwide(self, n: $crate::UWide) -> (Self, $crate::UWide) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_uwide(n)
            } else {
                match self.checked_div_rem_uwide(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Get the quotient of our big integer divided by [`UWide`][crate::UWide].
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_uwide(self, n: $crate::UWide) -> Self {
            self.div_rem_uwide(n).0
        }

        /// Get the remainder of our big integer divided by [`UWide`][crate::UWide].
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_uwide(self, n: $crate::UWide) -> $crate::UWide {
            self.div_rem_uwide(n).1
        }
    };

    (fixed) => {

        // U32

        /// Add [`u32`] to the big integer.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(addition)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn add_u32(self, n: u32) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_add_u32(n)
            } else {
                match self.checked_add_u32(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Subtract [`u32`] from the big integer.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(subtraction)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn sub_u32(self, n: u32) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_sub_u32(n)
            } else {
                match self.checked_sub_u32(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to subtract with overflow"),
                }
            }
        }

        /// Multiply our big integer by [`u32`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(multiplication)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn mul_u32(self, n: u32) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_u32(n)
            } else {
                match self.checked_mul_u32(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to multiply with overflow"),
                }
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`u32`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_rem_u32(self, n: u32) -> (Self, u32) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_u32(n)
            } else {
                match self.checked_div_rem_u32(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Get the quotient of our big integer divided by [`u32`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_u32(self, n: u32) -> Self {
            self.div_rem_u32(n).0
        }

        /// Get the remainder of our big integer divided by [`u32`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_u32(self, n: u32) -> u32 {
            self.div_rem_u32(n).1
        }

        // U64

        /// Add [`u64`] to the big integer.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(addition)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn add_u64(self, n: u64) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_add_u64(n)
            } else {
                match self.checked_add_u64(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Subtract [`u64`] from the big integer.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(subtraction)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn sub_u64(self, n: u64) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_sub_u64(n)
            } else {
                match self.checked_sub_u64(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to subtract with overflow"),
                }
            }
        }

        /// Multiply our big integer by [`u64`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(multiplication)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn mul_u64(self, n: u64) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_u64(n)
            } else {
                match self.checked_mul_u64(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to multiply with overflow"),
                }
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`u64`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_rem_u64(self, n: u64) -> (Self, u64) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_u64(n)
            } else {
                match self.checked_div_rem_u64(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Get the quotient of our big integer divided by [`u64`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_u64(self, n: u64) -> Self {
            self.div_rem_u64(n).0
        }

        /// Get the remainder of our big integer divided by [`u64`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_u64(self, n: u64) -> u64 {
            self.div_rem_u64(n).1
        }

        // U128

         /// Add [`u128`] to the big integer.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(addition)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn add_u128(self, n: u128) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_add_u128(n)
            } else {
                match self.checked_add_u128(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Subtract [`u128`] from the big integer.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(subtraction)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn sub_u128(self, n: u128) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_sub_u128(n)
            } else {
                match self.checked_sub_u128(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to subtract with overflow"),
                }
            }
        }

        /// Multiply our big integer by [`u128`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(multiplication)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn mul_u128(self, n: u128) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_u128(n)
            } else {
                match self.checked_mul_u128(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to multiply with overflow"),
                }
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`u128`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_rem_u128(self, n: u128) -> (Self, u128) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_u128(n)
            } else {
                match self.checked_div_rem_u128(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Get the quotient of our big integer divided by [`u128`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_u128(self, n: u128) -> Self {
            self.div_rem_u128(n).0
        }

        /// Get the remainder of our big integer divided by [`u128`].
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_u128(self, n: u128) -> u128 {
            self.div_rem_u128(n).1
        }
    };

    (@wrapping) => {
        // LIMB

        /// Get the quotient of our big integer divided by [`ULimb`][crate::ULimb],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_ulimb(self, n: $crate::ULimb) -> Self {
            self.wrapping_div_rem_ulimb(n).0
        }

        /// Get the remainder of our big integer divided by [`ULimb`][crate::ULimb],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_rem_ulimb(self, n: $crate::ULimb) -> $crate::ULimb {
            self.wrapping_div_rem_ulimb(n).1
        }

        // WIDE

        /// Get the quotient of our big integer divided by [`UWide`][crate::UWide],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_uwide(self, n: $crate::UWide) -> Self {
            self.wrapping_div_rem_uwide(n).0
        }

        /// Get the remainder of our big integer divided by [`UWide`][crate::UWide],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_rem_uwide(self, n: $crate::UWide) -> $crate::UWide {
            self.wrapping_div_rem_uwide(n).1
        }
    };

    (@wrapping-fixed) => {

        // U32

        /// Get the quotient of our big integer divided by [`u32`],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_u32(self, n: u32) -> Self {
            self.wrapping_div_rem_u32(n).0
        }

        /// Get the remainder of our big integer divided by [`u32`],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_rem_u32(self, n: u32) -> u32 {
            self.wrapping_div_rem_u32(n).1
        }

        // U64

        /// Get the quotient of our big integer divided by [`u64`],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_u64(self, n: u64) -> Self {
            self.wrapping_div_rem_u64(n).0
        }

        /// Get the remainder of our big integer divided by [`u64`],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_rem_u64(self, n: u64) -> u64 {
            self.wrapping_div_rem_u64(n).1
        }

        // U128

        /// Get the quotient of our big integer divided by [`u128`],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_u128(self, n: u128) -> Self {
            self.wrapping_div_rem_u128(n).0
        }

        /// Get the remainder of our big integer divided by [`u128`],
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_rem_u128(self, n: u128) -> u128 {
            self.wrapping_div_rem_u128(n).1
        }
    };

    (@overflowing) => {
        // LIMB

        /// Get the quotient and remainder of our big integer divided
        /// by [`ULimb`][crate::ULimb], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline]
        pub fn overflowing_div_rem_ulimb(self, n: $crate::ULimb) -> ((Self, $crate::ULimb), bool) {
            (self.wrapping_div_rem_ulimb(n), false)
        }

        /// Get the quotient of our big integer divided
        /// by [`ULimb`][crate::ULimb], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ulimb(n);
            (value.0, overflowed)
        }

        /// Get the remainder of our big integer divided
        /// by [`ULimb`][crate::ULimb], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem_ulimb(self, n: $crate::ULimb) -> ($crate::ULimb, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ulimb(n);
            (value.1, overflowed)
        }

        // WIDE

        /// Get the quotient and remainder of our big integer divided
        /// by [`UWide`][crate::UWide], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline]
        pub fn overflowing_div_rem_uwide(self, n: $crate::UWide) -> ((Self, $crate::UWide), bool) {
            (self.wrapping_div_rem_uwide(n), false)
        }

        /// Get the quotient of our big integer divided
        /// by [`UWide`][crate::UWide], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_uwide(self, n: $crate::UWide) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_uwide(n);
            (value.0, overflowed)
        }

        /// Get the remainder of our big integer divided
        /// by [`UWide`][crate::UWide], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem_uwide(self, n: $crate::UWide) -> ($crate::UWide, bool) {
            let (value, overflowed) = self.overflowing_div_rem_uwide(n);
            (value.1, overflowed)
        }
    };

    (@overflowing-fixed) => {
        // U32

        /// Get the quotient and remainder of our big integer divided
        /// by [`u32`], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline]
        pub fn overflowing_div_rem_u32(self, n: u32) -> ((Self, u32), bool) {
            (self.wrapping_div_rem_u32(n), false)
        }

        /// Get the quotient of our big integer divided
        /// by [`u32`], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_u32(self, n: u32) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_u32(n);
            (value.0, overflowed)
        }

        /// Get the remainder of our big integer divided
        /// by [`u32`], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem_u32(self, n: u32) -> (u32, bool) {
            let (value, overflowed) = self.overflowing_div_rem_u32(n);
            (value.1, overflowed)
        }

        // U64

        /// Get the quotient and remainder of our big integer divided
        /// by [`u64`], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline]
        pub fn overflowing_div_rem_u64(self, n: u64) -> ((Self, u64), bool) {
            (self.wrapping_div_rem_u64(n), false)
        }

        /// Get the quotient of our big integer divided
        /// by [`u64`], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_u64(self, n: u64) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_u64(n);
            (value.0, overflowed)
        }

        /// Get the remainder of our big integer divided
        /// by [`u64`], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem_u64(self, n: u64) -> (u64, bool) {
            let (value, overflowed) = self.overflowing_div_rem_u64(n);
            (value.1, overflowed)
        }

        // U128

        /// Get the quotient and remainder of our big integer divided
        /// by [`u128`], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline]
        pub fn overflowing_div_rem_u128(self, n: u128) -> ((Self, u128), bool) {
            (self.wrapping_div_rem_u128(n), false)
        }

        /// Get the quotient of our big integer divided
        /// by [`u128`], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_u128(self, n: u128) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_u128(n);
            (value.0, overflowed)
        }

        /// Get the remainder of our big integer divided
        /// by [`u128`], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem_u128(self, n: u128) -> (u128, bool) {
            let (value, overflowed) = self.overflowing_div_rem_u128(n);
            (value.1, overflowed)
        }
    };

    (@checked) => {
        // LIMB

        /// Add [`ULimb`][crate::ULimb] to the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_add_ulimb(self, n: $crate::ULimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_ulimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract [`ULimb`][crate::ULimb] from the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_sub_ulimb(self, n: $crate::ULimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_ulimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Multiply our big integer by [`ULimb`][crate::ULimb], returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_mul_ulimb(self, n: $crate::ULimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_ulimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline]
        pub fn checked_div_rem_ulimb(self, n: $crate::ULimb) -> Option<(Self, $crate::ULimb)> {
            if n == 0 {
                None
            } else {
                Some(self.wrapping_div_rem_ulimb(n))
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_div_ulimb(self, n: $crate::ULimb) -> Option<Self> {
            Some(self.checked_div_rem_ulimb(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_rem_ulimb(self, n: $crate::ULimb) -> Option<$crate::ULimb> {
            Some(self.checked_div_rem_ulimb(n)?.1)
        }

        // WIDE

        /// Add [`UWide`][crate::UWide] to the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_add_uwide(self, n: $crate::UWide) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_uwide(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract [`UWide`][crate::UWide] from the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_sub_uwide(self, n: $crate::UWide) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_uwide(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Multiply our big integer by [`UWide`][crate::UWide], returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_mul_uwide(self, n: $crate::UWide) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_uwide(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline]
        pub fn checked_div_rem_uwide(self, n: $crate::UWide) -> Option<(Self, $crate::UWide)> {
            if n == 0 {
                None
            } else {
                Some(self.wrapping_div_rem_uwide(n))
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_div_uwide(self, n: $crate::UWide) -> Option<Self> {
            Some(self.checked_div_rem_uwide(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_rem_uwide(self, n: $crate::UWide) -> Option<$crate::UWide> {
            Some(self.checked_div_rem_uwide(n)?.1)
        }
    };

    (@checked-fixed) => {
        // U32

        /// Add [`u32`] to the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(addition)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_add_u32(self, n: u32) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_u32(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract [`u32`] from the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(addition)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_sub_u32(self, n: u32) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_u32(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Multiply our big integer by [`u32`], returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(multiplication)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_mul_u32(self, n: u32) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_u32(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline]
        pub fn checked_div_rem_u32(self, n: u32) -> Option<(Self, u32)> {
            if n == 0 {
                None
            } else {
                Some(self.wrapping_div_rem_u32(n))
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_div_u32(self, n: u32) -> Option<Self> {
            Some(self.checked_div_rem_u32(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_rem_u32(self, n: u32) -> Option<u32> {
            Some(self.checked_div_rem_u32(n)?.1)
        }

        // U64

        /// Add [`u64`] to the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(addition)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_add_u64(self, n: u64) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_u64(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract [`u64`] from the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(addition)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_sub_u64(self, n: u64) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_u64(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Multiply our big integer by [`u64`], returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(multiplication)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_mul_u64(self, n: u64) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_u64(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline]
        pub fn checked_div_rem_u64(self, n: u64) -> Option<(Self, u64)> {
            if n == 0 {
                None
            } else {
                Some(self.wrapping_div_rem_u64(n))
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_div_u64(self, n: u64) -> Option<Self> {
            Some(self.checked_div_rem_u64(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_rem_u64(self, n: u64) -> Option<u64> {
            Some(self.checked_div_rem_u64(n)?.1)
        }

        // U128

        /// Add [`u128`] to the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(addition)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_add_u128(self, n: u128) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_u128(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract [`u128`] from the big integer, returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(addition)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_sub_u128(self, n: u128) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_u128(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Multiply our big integer by [`u128`], returning `None` on overflow.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(multiplication)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_mul_u128(self, n: u128) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_u128(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline]
        pub fn checked_div_rem_u128(self, n: u128) -> Option<(Self, u128)> {
            if n == 0 {
                None
            } else {
                Some(self.wrapping_div_rem_u128(n))
            }
        }

        /// Get the quotient of our big integer divided by an unsigned
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_div_u128(self, n: u128) -> Option<Self> {
            Some(self.checked_div_rem_u128(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning `None` on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::fixed_doc!(division)]
        #[cfg_attr(docsrs, doc(cfg(feature = "stdint")))]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_rem_u128(self, n: u128) -> Option<u128> {
            Some(self.checked_div_rem_u128(n)?.1)
        }
    };

    (@all) => {
        $crate::shared::limb::define!();
        $crate::shared::limb::define!(@wrapping);
        $crate::shared::limb::define!(@overflowing);
        $crate::shared::limb::define!(@checked);

        #[cfg(feature = "stdint")]
        $crate::shared::limb::define!(fixed);
        #[cfg(feature = "stdint")]
        $crate::shared::limb::define!(@wrapping-fixed);
        #[cfg(feature = "stdint")]
        $crate::shared::limb::define!(@overflowing-fixed);
        #[cfg(feature = "stdint")]
        $crate::shared::limb::define!(@checked-fixed);
    };
}

pub(crate) use define;
