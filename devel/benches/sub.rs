#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::*;

macro_rules! add_group {
    ($name:ident, $strategy:expr, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("sub");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);
            add_benches!(group, $strategy, rng, $prefix, wrapping_sub);

            let wide_data = get_wide_data($strategy, &mut rng);
            add_bench!(group, concat!($prefix, "::u256-wide"), wide_data.iter(), |x: &(
                u256,
                u128
            )| x
                .0
                .wrapping_sub_uwide(x.1));
        }
    };
}

add_group!(sub_uniform, RandomGen::Uniform, "uniform");
add_group!(sub_simple, RandomGen::Simple, "simple");
add_group!(sub_large, RandomGen::Large, "large");

criterion_group!(sub_random_benches, sub_uniform, sub_simple, sub_large);
criterion_main!(sub_random_benches);
