//! Bitwise operations for our types.

macro_rules! define {
    (
        signed_type => $s_t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        $crate::shared::bitops::define!(
            type => $s_t,
            wide_type => $wide_t,
            see_type => $see_t
        );

        #[inline(always)]
        #[doc = $crate::shared::bitops::wrapping_shl_doc!($see_t)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_shl(self, rhs: u32) -> Self {
            let result = $crate::math::shift::left_uwide(self.to_ne_wide(), rhs % Self::BITS);
            Self::from_ne_wide(result)
        }

        #[inline(always)]
        #[doc = $crate::shared::bitops::wrapping_shr_doc!($see_t)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_shr(self, rhs: u32) -> Self {
            let result = $crate::math::shift::right_uwide(self.to_ne_wide(), rhs % Self::BITS);
            Self::from_ne_wide(result)
        }

        /// Returns the minimum number of bits required to represent `self`.
        ///
        /// This method returns zero if `self` is zero.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, bit_width)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        #[inline(always)]
        pub const fn bit_width(self) -> u32 {
            Self::BITS - self.leading_zeros()
        }

        // Implementation detail of `isolate_highest_one`,
        // but can't be local to that function's body because the compiler
        // complains about the use of `Self` in local constants.
        const HIGH_ONE: Self = Self::from_ulimb(1).strict_shl(Self::BITS - 1);

        /// Returns `self` with only the most significant bit set, or `0` if
        /// the input is `0`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, isolate_highest_one)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        #[inline(always)]
        pub const fn isolate_highest_one(self) -> Self {
            self.bitand_const(Self::HIGH_ONE.wrapping_shr(self.leading_zeros()))
        }

        /// Returns `self` with only the least significant bit set, or `0` if
        /// the input is `0`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, isolate_lowest_one)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        #[inline(always)]
        pub const fn isolate_lowest_one(self) -> Self {
            self.bitand_const(self.wrapping_neg())
        }

        /// Returns the index of the highest bit set to one in `self`,
        /// or `None` if `self` is `0`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, highest_one)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        #[inline(always)]
        pub const fn highest_one(self) -> Option<u32> {
            (Self::BITS - 1).checked_sub(self.leading_zeros())
        }

        /// Returns the index of the lowest bit set to one in `self`,
        /// or `None` if `self` is `0`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, lowest_one)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        #[inline(always)]
        pub const fn lowest_one(self) -> Option<u32> {
            self.checked_ilog2()
        }
    };
}

pub(crate) use define;
