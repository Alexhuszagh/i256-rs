//! Helpers and logic for working with traits.

macro_rules! define {
    (
        type => $t:ident,
        unsigned_type => $u_t:ty $(,)?
    ) => {
        $crate::shared::traits::define!(impl => $t);
        $crate::shared::shift::define! { big => $t, impl => $u_t }
        $crate::shared::shift::define! { reference => $t, impl => $u_t }

        impl core::ops::Neg for $t {
            type Output = Self;

            #[inline(always)]
            fn neg(self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_neg()
                } else {
                    match self.checked_neg() {
                        Some(v) => v,
                        _ => core::panic!("attempt to negate with overflow"),
                    }
                }
            }
        }

        $crate::shared::traits::define!(ref => $t, impl => core::ops::Neg, op => neg,);

        impl core::str::FromStr for $t {
            type Err = $crate::ParseIntError;

            /// Parses a string s to return a value of this type.
            ///
            /// This is not optimized, since all optimization is done in
            /// theimplementation.
            #[inline]
            fn from_str(src: &str) -> Result<Self, $crate::ParseIntError> {
                // up to 39 digits can be stored in a `u128`, so less is always valid
                // meanwhile, 78 is good for all 256-bit integers. 32-bit architectures
                // on average have poor support for 128-bit operations so we try to use `u64`.
                if (cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32"))
                    && src.len() < 19
                {
                    Ok(Self::from_i64(i64::from_str(src)?))
                } else if src.len() < 39 {
                    Ok(Self::from_i128(i128::from_str(src)?))
                } else {
                    Self::from_str_radix(src, 10)
                }
            }
        }

        impl core::fmt::Binary for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: Binary for negative numbers uses wrapping formats.
                core::fmt::Binary::fmt(&self.as_unsigned(), f)
            }
        }

        impl core::fmt::Display for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                if self.is_negative() {
                    write!(f, "-")?;
                } else if f.sign_plus() {
                    write!(f, "+")?;
                }
                core::fmt::Display::fmt(&self.unsigned_abs(), f)
            }
        }

        impl core::fmt::LowerExp for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                if self.is_negative() {
                    write!(f, "-")?;
                } else if f.sign_plus() {
                    write!(f, "+")?;
                }
                core::fmt::LowerExp::fmt(&self.unsigned_abs(), f)
            }
        }

        impl core::fmt::LowerHex for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: LowerHex for negative numbers uses wrapping formats.
                core::fmt::LowerHex::fmt(&self.as_unsigned(), f)
            }
        }

        impl core::fmt::Octal for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: Octal for negative numbers uses wrapping formats.
                core::fmt::Octal::fmt(&self.as_unsigned(), f)
            }
        }

        impl core::fmt::UpperExp for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                if self.is_negative() {
                    write!(f, "-")?;
                } else if f.sign_plus() {
                    write!(f, "+")?;
                }
                core::fmt::UpperExp::fmt(&self.unsigned_abs(), f)
            }
        }

        impl core::fmt::UpperHex for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: UpperHex for negative numbers uses wrapping formats.
                core::fmt::UpperHex::fmt(&self.as_unsigned(), f)
            }
        }

        $crate::shared::traits::define! {
            to => $t, from => i8, op => from_i8,
            to => $t, from => i16, op => from_i16,
            to => $t, from => i32, op => from_i32,
            to => $t, from => i64, op => from_i64,
            to => $t, from => i128, op => from_i128,
        }

        impl TryFrom<$u_t> for $t {
            type Error = $crate::TryFromIntError;

            #[inline(always)]
            fn try_from(u: $u_t) -> Result<Self, $crate::TryFromIntError> {
                if u < Self::MAX.as_unsigned() {
                    Ok(u.as_signed())
                } else {
                    Err($crate::TryFromIntError {})
                }
            }
        }

        #[cfg(feature = "num-traits")]
        impl ::num_traits::Signed for $t {
            #[inline(always)]
            fn abs(&self) -> Self {
                Self::abs(*self)
            }

            #[inline]
            fn abs_sub(&self, other: &Self) -> Self {
                if self < other {
                    <Self as ::num_traits::ConstZero>::ZERO
                } else {
                    *self - *other
                }
            }

            #[inline]
            fn signum(&self) -> Self {
                if *self == <Self as ::num_traits::ConstZero>::ZERO {
                    <Self as ::num_traits::ConstZero>::ZERO
                } else if *self > <Self as ::num_traits::ConstZero>::ZERO {
                    <Self as ::num_traits::ConstOne>::ONE
                } else {
                    -<Self as ::num_traits::ConstOne>::ONE
                }
            }

            #[inline(always)]
            fn is_positive(&self) -> bool {
                *self >= <Self as ::num_traits::ConstZero>::ZERO
            }

            #[inline(always)]
            fn is_negative(&self) -> bool {
                *self < <Self as ::num_traits::ConstZero>::ZERO
            }
        }

        #[cfg(feature = "num-traits")]
        impl ::num_traits::FromPrimitive for $t {
            #[inline(always)]
            fn from_i8(n: i8) -> Option<Self> {
                Some(Self::from_i8(n))
            }

            #[inline(always)]
            fn from_i16(n: i16) -> Option<Self> {
                Some(Self::from_i16(n))
            }

            #[inline(always)]
            fn from_i32(n: i32) -> Option<Self> {
                Some(Self::from_i32(n))
            }

            #[inline(always)]
            fn from_i64(n: i64) -> Option<Self> {
                Some(Self::from_i64(n))
            }

            #[inline(always)]
            fn from_i128(n: i128) -> Option<Self> {
                Some(Self::from_i128(n))
            }

            #[inline(always)]
            fn from_isize(n: isize) -> Option<Self> {
                Some(Self::from_i128(n as i128))
            }

            #[inline(always)]
            fn from_u8(n: u8) -> Option<Self> {
                Some(Self::from_u8(n))
            }

            #[inline(always)]
            fn from_u16(n: u16) -> Option<Self> {
                Some(Self::from_u16(n))
            }

            #[inline(always)]
            fn from_u32(n: u32) -> Option<Self> {
                Some(Self::from_u32(n))
            }

            #[inline(always)]
            fn from_u64(n: u64) -> Option<Self> {
                Some(Self::from_u64(n))
            }

            #[inline(always)]
            fn from_u128(n: u128) -> Option<Self> {
                Some(Self::from_u128(n))
            }

            #[inline(always)]
            fn from_usize(n: usize) -> Option<Self> {
                Some(Self::from_u128(n as u128))
            }

            #[inline(always)]
            fn from_f32(_: f32) -> Option<Self> {
                unimplemented!("floating-point conversions")
            }

            #[inline(always)]
            fn from_f64(_: f64) -> Option<Self> {
                unimplemented!("floating-point conversions")
            }
        }

        #[cfg(feature = "num-traits")]
        impl ::num_traits::ToPrimitive for $t {
            #[inline]
            fn to_i8(&self) -> Option<i8> {
                const ABOVE: $t = <$t>::from_i8(i8::MAX);
                const BELOW: $t = <$t>::from_i8(i8::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_i8(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_i16(&self) -> Option<i16> {
                const ABOVE: $t = <$t>::from_i16(i16::MAX);
                const BELOW: $t = <$t>::from_i16(i16::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_i16(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_i32(&self) -> Option<i32> {
                const ABOVE: $t = <$t>::from_i32(i32::MAX);
                const BELOW: $t = <$t>::from_i32(i32::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_i32(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_i64(&self) -> Option<i64> {
                const ABOVE: $t = <$t>::from_i64(i64::MAX);
                const BELOW: $t = <$t>::from_i64(i64::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_i64(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_i128(&self) -> Option<i128> {
                const ABOVE: $t = <$t>::from_i128(i128::MAX);
                const BELOW: $t = <$t>::from_i128(i128::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_i128(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_isize(&self) -> Option<isize> {
                const ABOVE: $t = <$t>::from_i128(isize::MAX as i128);
                const BELOW: $t = <$t>::from_i128(isize::MIN as i128);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_i128(self) as isize)
                } else {
                    None
                }
            }

            #[inline]
            fn to_u8(&self) -> Option<u8> {
                const ABOVE: $t = <$t>::from_u8(u8::MAX);
                const BELOW: $t = <$t>::from_u8(u8::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_u8(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_u16(&self) -> Option<u16> {
                const ABOVE: $t = <$t>::from_u16(u16::MAX);
                const BELOW: $t = <$t>::from_u16(u16::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_u16(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_u32(&self) -> Option<u32> {
                const ABOVE: $t = <$t>::from_u32(u32::MAX);
                const BELOW: $t = <$t>::from_u32(u32::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_u32(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_u64(&self) -> Option<u64> {
                const ABOVE: $t = <$t>::from_u64(u64::MAX);
                const BELOW: $t = <$t>::from_u64(u64::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_u64(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_u128(&self) -> Option<u128> {
                const ABOVE: $t = <$t>::from_u128(u128::MAX);
                const BELOW: $t = <$t>::from_u128(u128::MIN);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_u128(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_usize(&self) -> Option<usize> {
                const ABOVE: $t = <$t>::from_u128(usize::MAX as u128);
                const BELOW: $t = <$t>::from_u128(usize::MIN as u128);
                if *self <= ABOVE && *self >= BELOW {
                    Some(Self::as_u128(self) as usize)
                } else {
                    None
                }
            }

            #[inline(always)]
            fn to_f32(&self) -> Option<f32> {
                unimplemented!("floating-point conversions")
            }

            #[inline(always)]
            fn to_f64(&self) -> Option<f64> {
                unimplemented!("floating-point conversions")
            }
        }

        #[cfg(feature = "num-traits")]
        impl ::num_traits::NumCast for $t {
            #[inline]
            fn from<T: ::num_traits::ToPrimitive>(n: T) -> Option<Self> {
                if let Some(n128i) = <T as ::num_traits::ToPrimitive>::to_i128(&n) {
                    <Self as ::num_traits::FromPrimitive>::from_i128(n128i)
                } else if let Some(n128u) = <T as ::num_traits::ToPrimitive>::to_u128(&n) {
                    <Self as ::num_traits::FromPrimitive>::from_u128(n128u)
                } else {
                    None
                }
            }
        }

        #[cfg(feature = "num-traits")]
        impl ::num_traits::PrimInt for $t {
            #[inline(always)]
            fn count_ones(self) -> u32 {
                Self::count_ones(self)
            }

            #[inline(always)]
            fn count_zeros(self) -> u32 {
                Self::count_zeros(self)
            }

            #[inline(always)]
            fn leading_ones(self) -> u32 {
                Self::leading_ones(self)
            }

            #[inline(always)]
            fn leading_zeros(self) -> u32 {
                Self::leading_zeros(self)
            }

            #[inline(always)]
            fn trailing_ones(self) -> u32 {
                Self::trailing_ones(self)
            }

            #[inline(always)]
            fn trailing_zeros(self) -> u32 {
                Self::trailing_zeros(self)
            }

            #[inline(always)]
            fn rotate_left(self, n: u32) -> Self {
                Self::rotate_left(self, n)
            }

            #[inline(always)]
            fn rotate_right(self, n: u32) -> Self {
                Self::rotate_right(self, n)
            }

            #[inline(always)]
            fn signed_shl(self, n: u32) -> Self {
                self << n
            }

            #[inline(always)]
            fn signed_shr(self, n: u32) -> Self {
                self >> n
            }

            #[inline(always)]
            fn unsigned_shl(self, n: u32) -> Self {
                (self.cast_unsigned() << n).cast_signed()
            }

            #[inline(always)]
            fn unsigned_shr(self, n: u32) -> Self {
                (self.cast_unsigned() >> n).cast_signed()
            }

            #[inline(always)]
            fn swap_bytes(self) -> Self {
                Self::swap_bytes(&self)
            }

            #[inline(always)]
            fn from_be(x: Self) -> Self {
                Self::from_be(x)
            }

            #[inline(always)]
            fn from_le(x: Self) -> Self {
                Self::from_le(x)
            }

            #[inline(always)]
            fn to_be(self) -> Self {
                Self::to_be(self)
            }

            #[inline(always)]
            fn to_le(self) -> Self {
                Self::to_le(self)
            }

            #[inline(always)]
            fn reverse_bits(self) -> Self {
                Self::reverse_bits(&self)
            }

            #[inline(always)]
            fn pow(self, exp: u32) -> Self {
                Self::pow(self, exp)
            }
        }
    };
}

pub(crate) use define;
