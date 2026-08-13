#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::*;

macro_rules! add_group {
    ($name:ident, $strategy:expr, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("shift");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);

            // unsigned
            let u128_udata = u128::gen_n::<3>($strategy, &mut rng, DEFAULT_COUNT);
            let bnum_udata: Vec<(BnumU256, u32)> =
                u128_udata.iter().map(|x| (to_bunum(x[0], x[1]), x[2] as u32)).collect();
            let crypto_udata: Vec<(CryptoU256, u32)> =
                u128_udata.iter().map(|x| (to_cryptobu(x[0], x[1]), x[2] as u32)).collect();
            let u256_udata: Vec<(i256::u256, u32)> =
                u128_udata.iter().map(|x| (to_u256(x[0], x[1]), x[2] as u32)).collect();

            add_bench!(
                group,
                concat!($prefix, "::unsigned-bnum-shl"),
                bnum_udata.iter(),
                bench_op!(wrapping_shl, BnumU256, u32)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-crypto-shl"),
                crypto_udata.iter(),
                |x: &(CryptoU256, u32)| x.0.shl(x.1 % 256)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-shl"),
                u256_udata.iter(),
                bench_op!(wrapping_shl, i256::u256, u32)
            );

            add_bench!(
                group,
                concat!($prefix, "::unsigned-bnum-shr"),
                bnum_udata.iter(),
                bench_op!(wrapping_shr, BnumU256, u32)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-crypto-shr"),
                crypto_udata.iter(),
                |x: &(CryptoU256, u32)| x.0.shr(x.1 % 256)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-shr"),
                u256_udata.iter(),
                bench_op!(wrapping_shr, i256::u256, u32)
            );
        }
    };
}

add_group!(shift_uniform, RandomGen::Uniform, "uniform");
add_group!(shift_simple, RandomGen::Simple, "simple");
add_group!(shift_large, RandomGen::Large, "large");

criterion_group!(shift_random_benches, shift_uniform, shift_simple, shift_large);
criterion_main!(shift_random_benches);
