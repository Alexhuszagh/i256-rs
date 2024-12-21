#[macro_use]
mod input;

use core::time::Duration;

use bnum::types::U256;
use criterion::{criterion_group, criterion_main, Criterion};
use i256::math::{wrapping_add_u128, wrapping_add_u32, wrapping_add_u64};
use input::{NumberRng, RandomGen};

const COUNT: usize = 10000;

native_op!(u32, u64, add_u32_native, wrapping_add);
native_op!(u64, u128, add_u64_native, wrapping_add);

#[inline]
fn add_bnum(x: U256, y: U256) -> U256 {
    x.wrapping_add(y)
}

macro_rules! add_bench {
    ($name:ident, $gen:ident, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("add");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);
            let u32_data = u32::gen_n::<4>(RandomGen::$gen, &mut rng, COUNT);
            let u64_data = u64::gen_n::<4>(RandomGen::$gen, &mut rng, COUNT);
            let u128_data = u128::gen_n::<4>(RandomGen::$gen, &mut rng, COUNT);
            let bnum_data: Vec<[U256; 2]> = u128_data
                .iter()
                .map(|x| [input::bnum_from_u128(x[0], x[1]), input::bnum_from_u128(x[2], x[3])])
                .collect();

            op_generator!(@4 group, concat!($prefix, "::u32-i256"), wrapping_add_u32, u32_data.iter());
            op_generator!(@4 group, concat!($prefix, "::u32-native"), add_u32_native, u32_data.iter());

            op_generator!(@4 group, concat!($prefix, "::u64-i256"), wrapping_add_u64, u64_data.iter());
            op_generator!(@4 group, concat!($prefix, "::u64-native"), add_u64_native, u64_data.iter());
            op_generator!(@4 group, concat!($prefix, "::u128-i256"), wrapping_add_u128, u128_data.iter());
            op_generator!(@2 group, concat!($prefix, "::u128-bnum"), add_bnum, bnum_data.iter());
        }
    }
}

add_bench!(add_uniform, Uniform, "uniform");
add_bench!(add_simple, Simple, "simple");
add_bench!(add_large, Large, "large");

criterion_group!(add_random_benches, add_uniform, add_simple, add_large);
criterion_main!(add_random_benches);
