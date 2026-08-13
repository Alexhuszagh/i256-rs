//! This tests the optimization of 3 different variants of multiplication
//! algorithms.

mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::{NumberRng, RandomGen};

const COUNT: usize = 50000;

macro_rules! mul {
    ($t:ty, $h:ty, $v1:ident, $v2:ident, $v3:ident, $narrow:ident) => {
        #[inline(always)]
        pub const fn $v1(x0: $t, x1: $t, y0: $t, y1: $t) -> ($t, $t) {
            let (lo, hi) = $narrow(x0, y0);
            let x0_y1 = x0.wrapping_mul(y1);
            let x1_y0 = x1.wrapping_mul(y0);
            let hi = hi.wrapping_add(x0_y1);
            let hi = hi.wrapping_add(x1_y0);
            (lo, hi)
        }

        #[inline(always)]
        pub const fn $narrow(x: $t, y: $t) -> ($t, $t) {
            const HALF: u32 = <$h>::BITS;
            const LO: $t = <$t>::MAX >> HALF;

            let (x0, x1) = (x & LO, x.wrapping_shr(HALF));
            let (y0, y1) = (y & LO, y.wrapping_shr(HALF));

            let x0_y0 = x0 * y0;
            let x0_y1 = x0 * y1;
            let x1_y0 = x1 * y0;
            let x1_y1 = x1 * y1;
            let (mut lo, mut c) = (x0_y0 & LO, x0_y0.wrapping_shr(HALF));

            c += x1_y0;
            lo += c.wrapping_shl(HALF);
            let mut hi = c.wrapping_shr(HALF);

            c = lo.wrapping_shr(HALF);
            lo &= LO;
            c += x0_y1;

            lo += c.wrapping_shl(HALF);
            hi += c.wrapping_shr(HALF);
            hi += x1_y1;

            (lo, hi)
        }

        #[inline(always)]
        pub const fn $v2(x0: $t, x1: $t, y0: $t, y1: $t) -> ($t, $t) {
            // NOTE: Unlike the others this is done in BE order
            const MASK: $t = <$h>::MAX as $t;
            const SHIFT: u32 = <$h>::BITS;
            let hi: [$t; 4] = [x1 >> SHIFT, x1 & MASK, x0 >> SHIFT, x0 & MASK];
            let lo: [$t; 4] = [y1 >> SHIFT, y1 & MASK, y0 >> SHIFT, y0 & MASK];
            let mut r: [[$t; 4]; 4] = [[0; 4]; 4];

            let mut y: usize = 4;
            while y > 0 {
                let y1 = y - 1;
                let mut x: usize = 4;
                while x > 0 {
                    let x1 = x - 1;
                    r[3 - x1][y1] = hi[x1] * lo[y1];
                    x -= 1;
                }
                y -= 1;
            }

            // first row
            let mut r_y0 = r[0][3] & MASK;
            let mut r_y1 = (r[0][2] & MASK) + (r[0][3] >> SHIFT);
            let mut x_y0 = (r[0][1] & MASK) + (r[0][2] >> SHIFT);
            let mut x_y1 = (r[0][0] & MASK) + (r[0][1] >> SHIFT);

            // second row
            r_y1 += r[1][3] & MASK;
            x_y0 += (r[1][2] & MASK) + (r[1][3] >> SHIFT);
            x_y1 += (r[1][1] & MASK) + (r[1][2] >> SHIFT);

            // third row
            x_y0 += r[2][3] & MASK;
            x_y1 += (r[2][2] & MASK) + (r[2][3] >> SHIFT);

            // fourth row
            x_y1 += r[3][3] & MASK;

            // move carry to next digit
            r_y1 += r_y0 >> SHIFT;
            x_y0 += r_y1 >> SHIFT;
            x_y1 += x_y0 >> SHIFT;

            // remove carry from current digit
            r_y0 &= MASK;
            r_y1 &= MASK;
            x_y0 &= MASK;
            x_y1 &= MASK;

            // combine components
            let hi = (x_y1 << SHIFT) | x_y0;
            let lo = (r_y1 << SHIFT) | r_y0;
            (lo, hi)
        }

        #[inline(always)]
        pub const fn $v3(x0: $t, x1: $t, y0: $t, y1: $t) -> ($t, $t) {
            // NOTE: This is for 2x wide converted to 4x half
            const N: usize = 4;
            const MASK: $t = <$h>::MAX as $t;
            const SHIFT: u32 = <$h>::BITS;
            let x: [$h; N] =
                [(x0 & MASK) as $h, (x0 >> SHIFT) as $h, (x1 & MASK) as $h, (x1 >> SHIFT) as $h];
            let y: [$h; N] =
                [(y0 & MASK) as $h, (y0 >> SHIFT) as $h, (y1 & MASK) as $h, (y1 >> SHIFT) as $h];
            let mut r: [$h; N] = [0; N];
            let mut carry: $h;

            let mut i: usize = 0;
            let mut j: usize;
            while i < N {
                carry = 0;
                j = 0;
                let xi = x[i];
                while j < N {
                    let ij = i + j;
                    let yj = y[j];
                    if ij < N {
                        let full = (xi as $t) * (yj as $t);
                        let prod = carry as $t + r[ij] as $t + full;
                        r[ij] = prod as $h;
                        carry = (prod >> SHIFT) as $h;
                    } else if xi != 0 && yj != 0 {
                        break;
                    }
                    j += 1;
                }
                i += 1;
            }
            let lo = ((r[1] as $t) << SHIFT) | (r[0] as $t);
            let hi = ((r[3] as $t) << SHIFT) | (r[2] as $t);
            (lo, hi)
        }
    };
}

mul!(u64, u32, mul64_v1, mul64_v2, mul64_v3, narrow64);
mul!(u128, u64, mul128_v1, mul128_v2, mul128_v3, narrow128);

macro_rules! bench {
    (@bench $group:ident, $func:ident, $name:expr, $iter:expr) => {
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|&x| {
                    std::hint::black_box($func(x[0], x[1], x[2], x[3]));
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
            let simple_data = <$t>::gen_n::<4>(RandomGen::Simple, &mut rng, COUNT);
            let large_data = <$t>::gen_n::<4>(RandomGen::Large, &mut rng, COUNT);

            bench!(@bench group, $v1, &format!("simple::{}", stringify!($v1)), simple_data.iter());
            bench!(@bench group, $v2, &format!("simple::{}", stringify!($v2)), simple_data.iter());
            bench!(@bench group, $v3, &format!("simple::{}", stringify!($v3)), simple_data.iter());

            bench!(@bench group, $v1, &format!("large::{}", stringify!($v1)), large_data.iter());
            bench!(@bench group, $v2, &format!("large::{}", stringify!($v2)), large_data.iter());
            bench!(@bench group, $v3, &format!("large::{}", stringify!($v3)), large_data.iter());
        }
    }
}

bench!(@group u64, mul64, mul64_v1, mul64_v2, mul64_v3);
bench!(@group u128, mul128, mul128_v1, mul128_v2, mul128_v3);

criterion_group!(mul, mul64, mul128);
criterion_main!(mul);
