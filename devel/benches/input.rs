#![allow(dead_code, unused_macros, unused_macro_rules)]

use core::mem;

use bnum::types::U256;
use fastrand::Rng;

#[derive(Copy, Clone, PartialEq, Eq)]
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
        for _ in 0..count {
            let mut value = [Self::default(); N];
            for i in 0..N {
                value[i] = Self::gen(strategy, rng);
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

macro_rules! op_generator {
    (@4 $group:ident, $name:expr, $func:ident, $iter:expr) => {{
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|&x| {
                    criterion::black_box($func(x[0], x[1], x[2], x[3]));
                })
            })
        });
    }};

    (@2 $group:ident, $name:expr, $func:ident, $iter:expr) => {{
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|&x| {
                    criterion::black_box($func(x[0], x[1]));
                })
            })
        });
    }};
}

macro_rules! native_op {
    ($t:ident, $w:ident, $name:ident, $op:ident) => {
        fn $name(x0: $t, x1: $t, y0: $t, y1: $t) -> ($t, $t) {
            let x: $w = (x0 as $w) | (x1 as $w) << $t::BITS;
            let y: $w = (y0 as $w) | (y1 as $w) << $t::BITS;
            let z = x.$op(y);
            (z as $t, (z >> $t::BITS) as $t)
        }
    };
}

pub fn bnum_from_u128(x: u128, y: u128) -> U256 {
    let buf = [x.to_le(), y.to_le()];
    // SAFETY: plain old data
    let slc = unsafe { mem::transmute::<[u128; 2], [u8; 32]>(buf) };
    U256::from_le_slice(&slc).unwrap()
}

pub fn bnum_from_u64(x0: u64, x1: u64, y0: u64, y1: u64) -> U256 {
    bnum_from_u128(x0 as u128 | (x1 as u128) << 64, y0 as u128 | (y1 as u128) << 64)
}
