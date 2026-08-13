#![allow(dead_code, unused_macros, unused_macro_rules)]

use std::mem;

pub use bnum::types::I256 as BnumI256;
pub use bnum::types::U256 as BnumU256;
pub use crypto_bigint::U256 as CryptoU256;
use fastrand::Rng;

pub const DEFAULT_COUNT: usize = 10000;

#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub enum RandomGen {
    // Generic
    Uniform,

    // Integers
    Simple,
    SimpleSigned,
    Large,
    LargeSigned,
}

pub trait NumberRng: Sized + Default + Copy {
    fn uniform(rng: &mut Rng) -> Self;
    fn simple(rng: &mut Rng) -> Self;
    fn large(rng: &mut Rng) -> Self;
    fn simple_signed(rng: &mut Rng) -> Self;
    fn large_signed(rng: &mut Rng) -> Self;
    fn zero() -> Self;

    #[inline]
    fn gen(strategy: RandomGen, rng: &mut Rng) -> Self {
        match strategy {
            RandomGen::Uniform => Self::uniform(rng),
            RandomGen::Simple => Self::simple(rng),
            RandomGen::SimpleSigned => Self::simple_signed(rng),
            RandomGen::Large => Self::large(rng),
            RandomGen::LargeSigned => Self::large_signed(rng),
        }
    }

    #[inline]
    fn gen_n<const N: usize>(strategy: RandomGen, rng: &mut Rng, count: usize) -> Vec<[Self; N]> {
        let mut vec: Vec<[Self; N]> = Vec::with_capacity(count);
        let is_simple = matches!(strategy, RandomGen::Simple | RandomGen::SimpleSigned);
        for _ in 0..count {
            let mut value = [Self::default(); N];
            for j in 0..N {
                value[j] = match (is_simple, j % 2) {
                    // NOTE: Simple should always have the hi digit as 0.
                    (true, 1) => Self::zero(),
                    _ => Self::gen(strategy, rng),
                };
            }
            vec.push(value);
        }
        vec
    }
}

macro_rules! unsigned_rng {
    ($($t:ident $smin:literal $smax:literal $lmin:literal $lmax:literal ; )*) => ($(
        impl NumberRng for $t {
            #[inline]
            fn uniform(rng: &mut Rng) -> $t {
                (rng.$t(<$t>::MIN..<$t>::MAX))
            }

            #[inline]
            fn simple(rng: &mut Rng) -> $t {
                (rng.$t($smin..$smax))
            }

            #[inline]
            fn simple_signed(_: &mut Rng) -> $t {
                unimplemented!()
            }

            #[inline]
            fn large(rng: &mut Rng) -> $t {
                (rng.$t($lmin..$lmax))
            }

            #[inline]
            fn large_signed(_: &mut Rng) -> $t {
                unimplemented!()
            }

            #[inline]
            fn zero() -> $t {
                0
            }
        }
    )*);
}

unsigned_rng! {
    u8 0 50 100 255 ;
    u16 0 1000 1024 65535 ;
    u32 0 1000 67108864 4294967295 ;
    u64 0 1000 288230376151711744 18446744073709551615 ;
    u128 0 1000 5316911983139663491615228241121378304 340282366920938463463374607431768211455 ;
}

macro_rules! signed_rng {
    ($(
        $t:ident
        $smin:literal $smax:literal $lmin:literal $lmax:literal
        $ssmin:literal $ssmax:literal $lsmin:literal $lsmax:literal
        ;
    )*) => ($(
        impl NumberRng for $t {
            #[inline]
            fn uniform(rng: &mut Rng) -> $t {
                (rng.$t(<$t>::MIN..<$t>::MAX))
            }

            #[inline]
            fn simple(rng: &mut Rng) -> $t {
                (rng.$t($smin..$smax))
            }

            #[inline]
            fn simple_signed(rng: &mut Rng) -> $t {
                (rng.$t($ssmin..$ssmax))
            }

            #[inline]
            fn large(rng: &mut Rng) -> $t {
                (rng.$t($lmin..$lmax))
            }

            #[inline]
            fn large_signed(rng: &mut Rng) -> $t {
                (rng.$t($lsmin..$lsmax))
            }

            #[inline]
            fn zero() -> $t {
                0
            }
        }
    )*);
}

signed_rng! {
    i8 0 50 100 127 -50 50 -127 -100 ;
    i16 0 1000 1024 32767 -1000 1000 -32767 -1024 ;
    i32 0 1000 67108864 2147483647 -1000 1000 -2147483647 -67108864 ;
    i64 0 1000 288230376151711744 9223372036854775807 -1000 1000 -9223372036854775807 -288230376151711744 ;
    i128 0 1000 5316911983139663491615228241121378304 170141183460469231731687303715884105727 -1000 1000 -170141183460469231731687303715884105727 -5316911983139663491615228241121378304 ;
}

macro_rules! add_bench {
    ($group:ident, $name:expr, $iter:expr, $func:expr) => {{
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|x| {
                    std::hint::black_box($func(x));
                })
            })
        });
    }};
}

macro_rules! bench_op {
    ($op:ident, $t:ty) => {
        |x: &($t, $t)| x.0.$op(x.1)
    };

    (@ref $op:ident, $t:ty) => {
        |x: &($t, $t)| x.0.$op(&x.1)
    };

    ($op:ident, $t:ty, $u:ty) => {
        |x: &($t, $u)| x.0.$op(x.1)
    };
}

pub fn to_bnum_udata(data: &[[u128; 4]]) -> Vec<(BnumU256, BnumU256)> {
    data.iter().map(|x| (to_bunum(x[0], x[1]), to_bunum(x[2], x[3]))).collect()
}

pub fn to_crypto_udata(data: &[[u128; 4]]) -> Vec<(CryptoU256, CryptoU256)> {
    data.iter().map(|x| (to_cryptobu(x[0], x[1]), to_cryptobu(x[2], x[3]))).collect()
}

pub fn to_u256_udata(data: &[[u128; 4]]) -> Vec<(i256::u256, i256::u256)> {
    data.iter().map(|x| (to_u256(x[0], x[1]), to_u256(x[2], x[3]))).collect()
}

pub fn to_ulimb_udata(data: &[[u128; 4]]) -> Vec<(i256::u256, i256::ULimb)> {
    data.iter().map(|x| (to_u256(x[0], x[1]), x[2] as i256::ULimb)).collect()
}

pub fn to_bnum_idata(data: &[[i128; 4]]) -> Vec<(BnumI256, BnumI256)> {
    data.iter().map(|x| (to_binum(x[0], x[1]), to_binum(x[2], x[3]))).collect()
}

pub fn to_i256_idata(data: &[[i128; 4]]) -> Vec<(i256::i256, i256::i256)> {
    data.iter().map(|x| (to_i256(x[0], x[1]), to_i256(x[2], x[3]))).collect()
}

pub fn to_ulimb_idata(data: &[[i128; 4]]) -> Vec<(i256::i256, i256::ULimb)> {
    data.iter().map(|x| (to_i256(x[0], x[1]), x[2] as i256::ULimb)).collect()
}

pub fn to_ilimb_idata(data: &[[i128; 4]]) -> Vec<(i256::i256, i256::ILimb)> {
    data.iter().map(|x| (to_i256(x[0], x[1]), x[2] as i256::ILimb)).collect()
}

pub fn to_bunum(x: u128, y: u128) -> BnumU256 {
    let buf = [x.to_le_bytes(), y.to_le_bytes()];
    // SAFETY: plain old data
    let slc = unsafe { mem::transmute::<[[u8; 16]; 2], [u8; 32]>(buf) };
    BnumU256::from_le_slice(&slc).unwrap()
}

pub fn to_binum(x: i128, y: i128) -> BnumI256 {
    let buf = [x.to_le_bytes(), y.to_le_bytes()];
    // SAFETY: plain old data
    let slc = unsafe { mem::transmute::<[[u8; 16]; 2], [u8; 32]>(buf) };
    BnumI256::from_le_slice(&slc).unwrap()
}

pub fn to_cryptobu(lo: u128, hi: u128) -> CryptoU256 {
    // SAFETY: plain old data
    let bytes: [u8; 32] = unsafe { mem::transmute([lo.to_le_bytes(), hi.to_le_bytes()]) };
    CryptoU256::from_le_slice(&bytes)
}

pub fn to_u256(x: u128, y: u128) -> i256::u256 {
    i256::u256::from_le_u64([x as u64, (x >> 64) as u64, y as u64, (y >> 64) as u64])
}

pub fn to_i256(x: i128, y: i128) -> i256::i256 {
    let x = x as u128;
    let y = y as u128;
    i256::i256::from_le_u64([x as u64, (x >> 64) as u64, y as u64, (y >> 64) as u64])
}
