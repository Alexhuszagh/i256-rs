#[macro_use]
mod util;

use i256::math::{div_rem_full, div_rem_limb, div_rem_wide};
use quickcheck::quickcheck;

fn u128_div(num: u128, den: u128) -> (u128, u128) {
    let x0 = num as u64;
    let x1 = (num >> 64) as u64;
    let y0 = den as u64;
    let y1 = (den >> 64) as u64;

    let num = [x0, x1];
    let den = [y0, y1];
    let (div, rem) = div_rem_full(&num, &den);

    let x0 = div[0] as u128;
    let x1 = div[1] as u128;
    let y0 = rem[0] as u128;
    let y1 = rem[1] as u128;

    (x0 | x1 << 64, y0 | y1 << 64)
}

fn u128_div_wide(num: u128, den: u64) -> (u128, u64) {
    let x0 = num as u64;
    let x1 = (num >> 64) as u64;

    let num = [x0, x1];
    let (div, rem) = div_rem_wide(&num, den as u128);

    let x0 = div[0] as u128;
    let x1 = div[1] as u128;

    (x0 | x1 << 64, rem as u64)
}

fn u128_div_limb(num: u128, den: u64) -> (u128, u64) {
    let x0 = num as u64;
    let x1 = (num >> 64) as u64;

    let num = [x0, x1];
    let (div, rem) = div_rem_limb(&num, den);

    let x0 = div[0] as u128;
    let x1 = div[1] as u128;

    (x0 | x1 << 64, rem)
}

quickcheck! {
    fn u128_div_quickcheck(num: u128, den: u128) -> bool {
        if den != 0 {
            let actual = u128_div(num, den);
            let div = num / den;
            let rem = num % den;
            actual == (div, rem)
        } else {
            true
        }
    }

    fn u128_div_wide_quickcheck(num: u128, den: u64) -> bool {
        if den != 0 {
            let actual = u128_div_wide(num, den);
            let div = num / (den as u128);
            let rem = num % (den as u128);
            actual == (div, rem as u64)
        } else {
            true
        }
    }

    fn u128_div_limb_quickcheck(num: u128, den: u64) -> bool {
        if den != 0 {
            let actual = u128_div_limb(num, den);
            let div = num / (den as u128);
            let rem = num % (den as u128);
            actual == (div, rem as u64)
        } else {
            true
        }
    }

    fn u256_div_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(wrap x0, x1, y0, y1, wrapping_div)
        } else {
            true
        }
    }
}
