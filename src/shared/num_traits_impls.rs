#[cfg(not(feature = "num-traits"))]
macro_rules! define {
    (type => $t:ty,) => {};
}

#[cfg(feature = "num-traits")]
macro_rules! define {
    // implementation of a 2-arg op trait
    (arity 2, $(
        type => $t:ty,
        impl => $trait:ident $(:: $ns1:ident)*,
        op => $op:ident,
        out => $out:ty,
    )*) => {$(
        impl $trait $(::$ns1)* for $t {
            #[inline(always)]
            fn $op(&self, rhs: &Self) -> $out {
                Self::$op(*self, *rhs)
            }
        }
    )*};

    // implementation of a 1-arg op trait
    (arity 1, $(
        type => $t:ty,
        impl => $trait:ident $(:: $ns1:ident)*,
        op => $op:ident,
        out => $out:ty,
    )*) => {$(
        impl $trait $(::$ns1)* for $t {
            #[inline(always)]
            fn $op(&self) -> $out {
                Self::$op(*self)
            }
        }
    )*};

    // implementation of a shift-like op trait
    (arity shift, $(
        type => $t:ty,
        impl => $trait:ident $(:: $ns1:ident)*,
        op => $op:ident,
        out => $out:ty,
    )*) => {$(
        impl $trait $(::$ns1)* for $t {
            #[inline(always)]
            fn $op(&self, rhs: u32) -> $out {
                Self::$op(*self, rhs)
            }
        }
    )*};

    // implementation of AsPrimitive, outbound
    (impl AsPrimitive, $(
        in => $in:ty,
        out => $out:ty,
        asop => $op:ident,
        $(extras => as $cast:ty,)?
    )*) => {$(
        impl ::num_traits::AsPrimitive<$out> for $in {
            fn as_(self) -> $out {
                <$in>::$op(&self) $(as $cast)?
            }
        }
    )*};

    // implementation of AsPrimitive, inbound
    (impl AsPrimitive, $(
        in => $in:ty,
        out => $out:ty,
        fromop => $op:ident,
        $(extras => as $cast:ty,)?
    )*) => {$(
        impl ::num_traits::AsPrimitive<$out> for $in {
            fn as_(self) -> $out {
                <$out>::$op(self $(as $cast)?)
            }
        }
    )*};

    // overall definition
    (
        type => $t:ty,
    ) => {
        impl ::num_traits::FromBytes for $t {
            type Bytes = [u8; <$t>::BYTES];

            #[inline(always)]
            fn from_be_bytes(bytes: &Self::Bytes) -> Self {
                Self::from_be_bytes(*bytes)
            }

            #[inline(always)]
            fn from_le_bytes(bytes: &Self::Bytes) -> Self {
                Self::from_le_bytes(*bytes)
            }
        }

        impl ::num_traits::ToBytes for $t {
            type Bytes = [u8; <$t>::BYTES];

            #[inline(always)]
            fn to_be_bytes(&self) -> Self::Bytes {
                Self::to_be_bytes(*self)
            }

            #[inline(always)]
            fn to_le_bytes(&self) -> Self::Bytes {
                Self::to_le_bytes(*self)
            }
        }

        impl ::num_traits::Bounded for $t {
            #[inline(always)]
            fn min_value() -> Self {
                Self::MIN
            }

            #[inline(always)]
            fn max_value() -> Self {
                Self::MAX
            }
        }

        impl ::num_traits::Zero for $t {
            #[inline(always)]
            fn zero() -> Self {
                <Self as ::num_traits::ConstZero>::ZERO
            }

            #[inline(always)]
            fn is_zero(&self) -> bool {
                *self == <Self as ::num_traits::ConstZero>::ZERO
            }
        }

        impl ::num_traits::ConstZero for $t {
            const ZERO: Self = Self::from_u8(0);
        }

        impl ::num_traits::One for $t {
            #[inline(always)]
            fn one() -> Self {
                <Self as ::num_traits::ConstOne>::ONE
            }

            #[inline(always)]
            fn is_one(&self) -> bool {
                *self == <Self as ::num_traits::ConstOne>::ONE
            }
        }

        impl ::num_traits::ConstOne for $t {
            const ONE: Self = Self::from_u8(1);
        }

        impl ::num_traits::MulAdd for $t {
            type Output = Self;

            #[inline]
            fn mul_add(self, a: Self, b: Self) -> Self {
                (self * a) + b
            }
        }

        impl ::num_traits::MulAddAssign for $t {
            #[inline(always)]
            fn mul_add_assign(&mut self, a: Self, b: Self) {
                *self = <Self as ::num_traits::MulAdd>::mul_add(*self, a, b)
            }
        }

        impl ::num_traits::Pow<u32> for $t {
            type Output = Self;

            #[inline(always)]
            fn pow(self, exp: u32) -> Self {
                Self::pow(self, exp)
            }
        }

        impl ::num_traits::Pow<&u32> for $t {
            type Output = Self;

            #[inline(always)]
            fn pow(self, exp: &u32) -> Self {
                Self::pow(self, *exp)
            }
        }

        impl ::num_traits::Euclid for $t {
            #[inline(always)]
            fn div_euclid(&self, v: &Self) -> Self {
                Self::div_euclid(*self, *v)
            }

            #[inline(always)]
            fn rem_euclid(&self, v: &Self) -> Self {
                Self::rem_euclid(*self, *v)
            }
        }

        impl ::num_traits::CheckedEuclid for $t {
            #[inline(always)]
            fn checked_div_euclid(&self, v: &Self) -> Option<Self> {
                Self::checked_div_euclid(*self, *v)
            }

            #[inline(always)]
            fn checked_rem_euclid(&self, v: &Self) -> Option<Self> {
                Self::checked_rem_euclid(*self, *v)
            }
        }

        impl ::num_traits::Num for $t {
            type FromStrRadixErr = $crate::ParseIntError;

            #[inline(always)]
            fn from_str_radix(src: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                Self::from_str_radix(src, radix)
            }
        }

        impl ::num_traits::Saturating for $t {
            #[inline(always)]
            fn saturating_add(self, v: Self) -> Self {
                Self::saturating_add(self, v)
            }

            #[inline(always)]
            fn saturating_sub(self, v: Self) -> Self {
                Self::saturating_sub(self, v)
            }
        }

        $crate::shared::num_traits_impls::define! {
            arity 2,
            type => $t, impl => num_traits::SaturatingAdd, op => saturating_add, out => $t,
            type => $t, impl => num_traits::SaturatingSub, op => saturating_sub, out => $t,
            type => $t, impl => num_traits::SaturatingMul, op => saturating_mul, out => $t,
            type => $t, impl => num_traits::WrappingAdd, op => wrapping_add, out => $t,
            type => $t, impl => num_traits::WrappingSub, op => wrapping_sub, out => $t,
            type => $t, impl => num_traits::WrappingMul, op => wrapping_mul, out => $t,
            type => $t, impl => num_traits::CheckedAdd, op => checked_add, out => Option<$t>,
            type => $t, impl => num_traits::CheckedSub, op => checked_sub, out => Option<$t>,
            type => $t, impl => num_traits::CheckedMul, op => checked_mul, out => Option<$t>,
            type => $t, impl => num_traits::CheckedDiv, op => checked_div, out => Option<$t>,
            type => $t, impl => num_traits::CheckedRem, op => checked_rem, out => Option<$t>,
        }

        $crate::shared::num_traits_impls::define! {
            arity 1,
            type => $t, impl => num_traits::WrappingNeg, op => wrapping_neg, out => $t,
            type => $t, impl => num_traits::CheckedNeg, op => checked_neg, out => Option<$t>,
        }

        $crate::shared::num_traits_impls::define! {
            arity shift,
            type => $t, impl => num_traits::WrappingShl, op => wrapping_shl, out => $t,
            type => $t, impl => num_traits::WrappingShr, op => wrapping_shr, out => $t,
            type => $t, impl => num_traits::CheckedShl, op => checked_shl, out => Option<$t>,
            type => $t, impl => num_traits::CheckedShr, op => checked_shr, out => Option<$t>,
        }

        $crate::shared::num_traits_impls::define! {
            impl AsPrimitive,
            in => $t, out => u8, asop => as_u8,
            in => $t, out => i8, asop => as_i8,
            in => $t, out => u16, asop => as_u16,
            in => $t, out => i16, asop => as_i16,
            in => $t, out => u32, asop => as_u32,
            in => $t, out => i32, asop => as_i32,
            in => $t, out => u64, asop => as_u64,
            in => $t, out => i64, asop => as_i64,
            in => $t, out => u128, asop => as_u128,
            in => $t, out => i128, asop => as_i128,
            in => $t, out => usize, asop => as_u128, extras => as usize,
            in => $t, out => isize, asop => as_i128, extras => as isize,
        }

        $crate::shared::num_traits_impls::define! {
            impl AsPrimitive,
            in => u8, out => $t, fromop => from_u8,
            in => i8, out => $t, fromop => from_i8,
            in => u16, out => $t, fromop => from_u16,
            in => i16, out => $t, fromop => from_i16,
            in => u32, out => $t, fromop => from_u32,
            in => i32, out => $t, fromop => from_i32,
            in => u64, out => $t, fromop => from_u64,
            in => i64, out => $t, fromop => from_i64,
            in => u128, out => $t, fromop => from_u128,
            in => i128, out => $t, fromop => from_i128,
            in => usize, out => $t, fromop => from_u128, extras => as u128,
            in => isize, out => $t, fromop => from_i128, extras => as i128,
            in => char, out => $t, fromop => from_u32, extras => as u32,
            in => bool, out => $t, fromop => from_u8, extras => as u8,
        }
    };
}

pub(crate) use define;
