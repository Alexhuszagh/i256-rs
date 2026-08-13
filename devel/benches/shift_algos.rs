//! This tests the optimization of 3 different variants of bitshifts.

mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::{NumberRng, RandomGen};

const COUNT: usize = 50000;

macro_rules! shl {
    ($t:ty, $v1:ident, $v2:ident, $v3:ident) => {
        #[inline(always)]
        pub const fn $v1(x0: $t, x1: $t, shift: u32) -> ($t, $t) {
            const BITS: u32 = <$t>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift left with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (0, x0.wrapping_shl(shift - BITS))
            } else if shift == 0 {
                (x0, x1)
            } else {
                let hi = x1.wrapping_shl(shift);
                let lo = x0.wrapping_shl(shift);
                let carry = x0.wrapping_shr(BITS - shift);
                (lo, hi | carry)
            }
        }

        #[inline(always)]
        pub const fn $v2(x0: $t, x1: $t, shift: u32) -> ($t, $t) {
            const BITS: u32 = <$t>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift left with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (0, x0.wrapping_shl(shift - BITS))
            } else {
                let hi = x1.wrapping_shl(shift);
                let lo = x0.wrapping_shl(shift);
                match x0.checked_shr(BITS - shift) {
                    Some(carry) => (lo, hi | carry),
                    None => (lo, hi),
                }
            }
        }

        #[inline(always)]
        pub const fn $v3(x0: $t, x1: $t, shift: u32) -> ($t, $t) {
            const BITS: u32 = <$t>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift left with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (0, x0.wrapping_shl(shift - BITS))
            } else {
                let hi = x1.wrapping_shl(shift);
                let lo = x0.wrapping_shl(shift);
                let carry = match x0.checked_shr(BITS - shift) {
                    Some(carry) => carry,
                    None => 0,
                };
                (lo, hi | carry)
            }
        }
    };
}

shl!(u64, shl64_v1, shl64_v2, shl64_v3);
shl!(u128, shl128_v1, shl128_v2, shl128_v3);

macro_rules! shr {
    ($t:ty, $v1:ident, $v2:ident, $v3:ident) => {
        #[inline(always)]
        pub const fn $v1(x0: $t, x1: $t, shift: u32) -> ($t, $t) {
            const BITS: u32 = <$t>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift left with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (0, x0.wrapping_shr(shift - BITS))
            } else if shift == 0 {
                (x0, x1)
            } else {
                let hi = x1.wrapping_shr(shift);
                let lo = x0.wrapping_shr(shift);
                let carry = x0.wrapping_shl(BITS - shift);
                (lo, hi | carry)
            }
        }

        #[inline(always)]
        pub const fn $v2(x0: $t, x1: $t, shift: u32) -> ($t, $t) {
            const BITS: u32 = <$t>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift left with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (0, x0.wrapping_shr(shift - BITS))
            } else {
                let hi = x1.wrapping_shr(shift);
                let lo = x0.wrapping_shr(shift);
                match x0.checked_shl(BITS - shift) {
                    Some(carry) => (lo, hi | carry),
                    None => (lo, hi),
                }
            }
        }

        #[inline(always)]
        pub const fn $v3(x0: $t, x1: $t, shift: u32) -> ($t, $t) {
            const BITS: u32 = <$t>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift left with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (0, x0.wrapping_shr(shift - BITS))
            } else {
                let hi = x1.wrapping_shr(shift);
                let lo = x0.wrapping_shr(shift);
                let carry = match x0.checked_shl(BITS - shift) {
                    Some(carry) => carry,
                    None => 0,
                };
                (lo, hi | carry)
            }
        }
    };
}

shr!(u64, shr64_v1, shr64_v2, shr64_v3);
shr!(u128, shr128_v1, shr128_v2, shr128_v3);

macro_rules! bench {
    (@bench $group:ident, $func:ident, $name:expr, $iter:expr) => {
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|&x| {
                    std::hint::black_box($func(x.0, x.1, x.2));
                })
            })
        });
    };

    (@group $t:ty, $func:ident, $v1:ident, $v2:ident, $v3:ident) => {
        fn $func(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group(stringify!($func));
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);
            let lo_data = <$t>::gen_n::<2>(RandomGen::Simple, &mut rng, COUNT);
            let hi_data = <$t>::gen_n::<2>(RandomGen::Large, &mut rng, COUNT);
            let simple_data: Vec<($t, $t, u32)> =
                lo_data.iter().map(|x| (x[0], x[1], rng.u32(0..64))).collect();
            let large_data: Vec<($t, $t, u32)> =
                hi_data.iter().map(|x| (x[0], x[1], rng.u32(0..64))).collect();

            bench!(@bench group, $v1, &format!("simple::{}", stringify!($v1)), simple_data.iter());
            bench!(@bench group, $v2, &format!("simple::{}", stringify!($v2)), simple_data.iter());
            bench!(@bench group, $v3, &format!("simple::{}", stringify!($v3)), simple_data.iter());

            bench!(@bench group, $v1, &format!("large::{}", stringify!($v1)), large_data.iter());
            bench!(@bench group, $v2, &format!("large::{}", stringify!($v2)), large_data.iter());
            bench!(@bench group, $v3, &format!("large::{}", stringify!($v3)), large_data.iter());
        }
    }
}

bench!(@group u64, shl64, shl64_v1, shl64_v2, shl64_v3);
bench!(@group u128, shl128, shl128_v1, shl128_v2, shl128_v3);
bench!(@group u64, shr64, shr64_v1, shr64_v2, shr64_v3);
bench!(@group u128, shr128, shr128_v1, shr128_v2, shr128_v3);

criterion_group!(shl, shl64, shl128);
criterion_group!(shr, shr64, shr128);
criterion_main!(shr);
