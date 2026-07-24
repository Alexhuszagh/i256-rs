//! Associated constants for our types.

#[rustfmt::skip]
macro_rules! define {
    (
        bits => $bits:expr,
        wide_type => $wide_t:ty,
        low_type => $lo_t:ty,
        high_type => $hi_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        /// The smallest value that can be represented by this integer type.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, MIN)]
        #[allow(deprecated)]
        pub const MIN: Self = Self::min_value();

        /// The largest value that can be represented by this integer type
        /// (2<sup>256</sup> - 1).
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, MAX)]
        #[allow(deprecated)]
        pub const MAX: Self = Self::max_value();

        /// A value that evaluates to 0.
        ///
        /// For values other than `0` and `1`, use the `from_*` conversion
        /// functions, such as [`Self::from_u64`].
        pub const ZERO: Self = Self::from_u8(0);

        /// A value that evaluates to 1.
        ///
        /// For values other than `0` and `1`, use the `from_*` conversion
        /// functions, such as [`Self::from_u64`].
        pub const ONE: Self = Self::from_u8(1);

        /// The size of this integer type in bits.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use i256::u256;
        /// assert_eq!(u256::BITS, 256);
        /// ```
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, BITS)]
        pub const BITS: u32 = $bits;

        // Internal use only

        /// The number of limbs in the type.
        pub(crate) const LIMBS: usize = Self::BITS as usize / 8 / core::mem::size_of::<$crate::ULimb>();

        /// The number of wide values in the type.
        pub(crate) const WIDE: usize = Self::BITS as usize / 8 / core::mem::size_of::<$crate::UWide>();
    };
}

pub(crate) use define;

#[rustfmt::skip]
macro_rules! min_value_doc {
    ($wide_t:ty) => {
        concat!(
"
New code should prefer to use  [`", stringify!($wide_t), "::MIN`] instead.

Returns the smallest value that can be represented by this integer type.

See [`", stringify!($wide_t), "::min_value`].
"
        )
    };
}

pub(crate) use min_value_doc;

#[rustfmt::skip]
macro_rules! max_value_doc {
    ($wide_t:ty) => {
        concat!(
"
New code should prefer to use  [`", stringify!($wide_t), "::MAX`] instead.

Returns the largest value that can be represented by this integer type.

See [`", stringify!($wide_t), "::max_value`].
"
        )
    };
}

pub(crate) use max_value_doc;

#[rustfmt::skip]
macro_rules! is_signed_doc {
    () => {
        "If the integer is signed, that is, can contain negative numbers."
    };
}

pub(crate) use is_signed_doc;
