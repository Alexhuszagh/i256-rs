//! Operations for our limb operations on big integers.

macro_rules! define {
    () => {
        /// Add an unsigned limb to the big integer.
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

        /// Subtract an unsigned limb from the big integer.
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

        /// Multiply our big integer by an unsigned limb.
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
        /// by an unsigned limb.
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

        /// Get the quotient of our big integer divided by an unsigned limb.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_ulimb(self, n: $crate::ULimb) -> Self {
            self.div_rem_ulimb(n).0
        }

        /// Get the remainder of our big integer divided by an unsigned limb.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_ulimb(self, n: $crate::ULimb) -> $crate::ULimb {
            self.div_rem_ulimb(n).1
        }
    };

    (@wrapping) => {
        /// Get the quotient of our big integer divided by an unsigned limb,
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_ulimb(self, n: $crate::ULimb) -> Self {
            self.wrapping_div_rem_ulimb(n).0
        }

        /// Get the remainder of our big integer divided by an unsigned limb,
        /// wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_rem_ulimb(self, n: $crate::ULimb) -> $crate::ULimb {
            self.wrapping_div_rem_ulimb(n).1
        }
    };

    (@overflowing) => {
        /// Get the quotient and remainder of our big integer divided
        /// by an unsigned limb, returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline]
        pub fn overflowing_div_rem_ulimb(self, n: $crate::ULimb) -> ((Self, $crate::ULimb), bool) {
            (self.wrapping_div_rem_ulimb(n), false)
        }

        /// Get the quotient of our big integer divided
        /// by an unsigned limb, returning the value and if overflow
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
        /// by an unsigned limb, returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem_ulimb(self, n: $crate::ULimb) -> ($crate::ULimb, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ulimb(n);
            (value.1, overflowed)
        }
    };

    (@checked) => {
        /// Add an unsigned limb to the big integer, returning None on overflow.
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

        /// Subtract an unsigned limb from the big integer, returning None on overflow.
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

        /// Multiply our big integer by an unsigned limb, returning None on overflow.
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
        /// limb, returning None on overflow or division by 0.
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
        /// limb, returning None on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_div_ulimb(self, n: $crate::ULimb) -> Option<Self> {
            Some(self.checked_div_rem_ulimb(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning None on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_rem_ulimb(self, n: $crate::ULimb) -> Option<$crate::ULimb> {
            Some(self.checked_div_rem_ulimb(n)?.1)
        }
    };

    (@all) => {
        $crate::shared::limb::define!();
        $crate::shared::limb::define!(@wrapping);
        $crate::shared::limb::define!(@overflowing);
        $crate::shared::limb::define!(@checked);
    };
}

pub(crate) use define;
