//! Helpers and logic for working with traits.

macro_rules! define {
    (
        type => $t:ident,
        signed_type => $s_t:ty $(,)?
    ) => {
        $crate::shared::traits::define!(impl => $t);
        $crate::shared::shift::define! { big => $t, impl => $s_t }
        $crate::shared::shift::define! { reference => $t, impl => $s_t }

        impl core::fmt::Binary for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 2);
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0b")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(bytes.len());
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                core::write!(f, "{}", formatted)
            }
        }

        impl core::fmt::Display for $t {
            #[inline]
            #[allow(clippy::bind_instead_of_map)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 10);
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                core::write!(f, "{}", formatted)
            }
        }

        impl core::fmt::LowerHex for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let count = self.to_str_radix(&mut buffer, 16).len();
                let lower = buffer.map(|x| x.to_ascii_lowercase());
                let bytes = &lower[buffer.len() - count..];
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0x")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(count);
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                f.write_str(formatted)
            }
        }

        impl core::fmt::UpperHex for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let count = self.to_str_radix(&mut buffer, 16).len();
                let upper = buffer.map(|x| x.to_ascii_uppercase());
                let bytes = &upper[buffer.len() - count..];
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0x")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(count);
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                f.write_str(formatted)
            }
        }

        impl core::fmt::LowerExp for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 10);
                let formatted = core::str::from_utf8(&bytes[1..]);
                let formatted = formatted.or_else(|_| Err(core::fmt::Error))?;
                core::write!(f, "{}.{}e{}", bytes[0] as char, formatted, bytes.len() - 1)
            }
        }

        impl core::fmt::UpperExp for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 10);
                let formatted = core::str::from_utf8(&bytes[1..]);
                let formatted = formatted.or_else(|_| Err(core::fmt::Error))?;
                core::write!(f, "{}.{}E{}", bytes[0] as char, formatted, bytes.len() - 1)
            }
        }

        impl core::fmt::Octal for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 8);
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0o")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(bytes.len());
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                core::write!(f, "{}", formatted)
            }
        }

        impl core::str::FromStr for $t {
            type Err = $crate::ParseIntError;

            /// Parses a string s to return a value of this type.
            ///
            /// This is not optimized, since all optimization is done in
            /// the lexical implementation.
            #[inline]
            fn from_str(src: &str) -> Result<Self, $crate::ParseIntError> {
                // up to 39 digits can be stored in a `u128`, so less is always valid
                // meanwhile, 78 is good for all 256-bit integers. 32-bit architectures
                // on average have poor support for 128-bit operations so we try to use `u64`.
                if (cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32"))
                    && src.len() < 20
                {
                    Ok(Self::from_u64(u64::from_str(src)?))
                } else if src.len() < 39 {
                    Ok(Self::from_u128(u128::from_str(src)?))
                } else {
                    Self::from_str_radix(src, 10)
                }
            }
        }

        $crate::shared::traits::define! {
            to => $t, tryfrom => i8, op => from_i8,
            to => $t, tryfrom => i16, op => from_i16,
            to => $t, tryfrom => i32, op => from_i32,
            to => $t, tryfrom => i64, op => from_i64,
            to => $t, tryfrom => i128, op => from_i128,
        }

        impl TryFrom<$s_t> for $t {
            type Error = $crate::TryFromIntError;

            #[inline(always)]
            fn try_from(u: $s_t) -> Result<Self, $crate::TryFromIntError> {
                if !u.is_negative() {
                    Ok(u.as_unsigned())
                } else {
                    Err($crate::TryFromIntError {})
                }
            }
        }

        #[cfg(feature = "num-traits")]
        impl ::num_traits::Unsigned for $t {}

        #[cfg(feature = "num-traits")]
        impl ::num_traits::FromPrimitive for $t {
            #[inline]
            fn from_i8(n: i8) -> Option<Self> {
                n.try_into().ok().map(Self::from_u8)
            }

            #[inline]
            fn from_i16(n: i16) -> Option<Self> {
                n.try_into().ok().map(Self::from_u16)
            }

            #[inline]
            fn from_i32(n: i32) -> Option<Self> {
                n.try_into().ok().map(Self::from_u32)
            }

            #[inline]
            fn from_i64(n: i64) -> Option<Self> {
                n.try_into().ok().map(Self::from_u64)
            }

            #[inline]
            fn from_i128(n: i128) -> Option<Self> {
                n.try_into().ok().map(Self::from_u128)
            }

            #[inline]
            fn from_isize(n: isize) -> Option<Self> {
                n.try_into().ok().map(Self::from_u128)
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

            #[inline]
            fn from_f32(_: f32) -> Option<Self> {
                unimplemented!("floating-point conversions")
            }

            #[inline]
            fn from_f64(_: f64) -> Option<Self> {
                unimplemented!("floating-point conversions")
            }
        }

        #[cfg(feature = "num-traits")]
        impl ::num_traits::ToPrimitive for $t {
            #[inline]
            fn to_i8(&self) -> Option<i8> {
                const ABOVE: $t = <$t>::from_i8(i8::MAX);
                if *self <= ABOVE {
                    Some(Self::as_i8(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_i16(&self) -> Option<i16> {
                const ABOVE: $t = <$t>::from_i16(i16::MAX);
                if *self <= ABOVE {
                    Some(Self::as_i16(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_i32(&self) -> Option<i32> {
                const ABOVE: $t = <$t>::from_i32(i32::MAX);
                if *self <= ABOVE {
                    Some(Self::as_i32(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_i64(&self) -> Option<i64> {
                const ABOVE: $t = <$t>::from_i64(i64::MAX);
                if *self <= ABOVE {
                    Some(Self::as_i64(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_i128(&self) -> Option<i128> {
                const ABOVE: $t = <$t>::from_i128(i128::MAX);
                if *self <= ABOVE {
                    Some(Self::as_i128(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_isize(&self) -> Option<isize> {
                const ABOVE: $t = <$t>::from_i128(isize::MAX as i128);
                if *self <= ABOVE {
                    Some(Self::as_i128(self) as isize)
                } else {
                    None
                }
            }

            #[inline]
            fn to_u8(&self) -> Option<u8> {
                const ABOVE: $t = <$t>::from_u8(u8::MAX);
                if *self <= ABOVE {
                    Some(Self::as_u8(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_u16(&self) -> Option<u16> {
                const ABOVE: $t = <$t>::from_u16(u16::MAX);
                if *self <= ABOVE {
                    Some(Self::as_u16(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_u32(&self) -> Option<u32> {
                const ABOVE: $t = <$t>::from_u32(u32::MAX);
                if *self <= ABOVE {
                    Some(Self::as_u32(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_u64(&self) -> Option<u64> {
                const ABOVE: $t = <$t>::from_u64(u64::MAX);
                if *self <= ABOVE {
                    Some(Self::as_u64(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_u128(&self) -> Option<u128> {
                const ABOVE: $t = <$t>::from_u128(u128::MAX);
                if *self <= ABOVE {
                    Some(Self::as_u128(self))
                } else {
                    None
                }
            }

            #[inline]
            fn to_usize(&self) -> Option<usize> {
                const ABOVE: $t = <$t>::from_u128(usize::MAX as u128);
                if *self <= ABOVE {
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
                if let Some(n128u) = <T as ::num_traits::ToPrimitive>::to_u128(&n) {
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
                (self.cast_signed() << n).cast_unsigned()
            }

            #[inline(always)]
            fn signed_shr(self, n: u32) -> Self {
                (self.cast_signed() >> n).cast_unsigned()
            }

            #[inline(always)]
            fn unsigned_shl(self, n: u32) -> Self {
                self << n
            }

            #[inline(always)]
            fn unsigned_shr(self, n: u32) -> Self {
                self >> n
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
