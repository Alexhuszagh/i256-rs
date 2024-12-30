//! Casts between primitive and signed <-> unsigned big integers.

#[rustfmt::skip]
macro_rules! define {
    (
        unsigned_type => $u_t:ty,
        bits => $bits:expr,
        wide_type => $wide_t:ty,
        kind => $kind:ident $(,)?
    ) => {
        $crate::shared::casts::define!(
            unsigned_type => $u_t,
            signed_type => Self,
            bits => $bits,
            kind => $kind,
        );

        /// Returns the bit pattern of `self` reinterpreted as an unsigned integer
        /// of the same size.
        ///
        /// This produces the same result as an `as` cast, but ensures that the
        /// bit-width remains the same.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::cast_unsigned`].")]
        #[inline(always)]
        pub const fn cast_unsigned(self) -> $u_t {
            self.as_unsigned()
        }
    };
}

pub(crate) use define;