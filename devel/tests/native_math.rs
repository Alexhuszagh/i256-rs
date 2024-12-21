use i256::math::*;
use quickcheck::quickcheck;

const LO32: u64 = u32::MAX as u64;

quickcheck! {
    fn add_u32_quickcheck(x: u64, y: u64) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let y0 = (y & LO32) as u32;
        let y1 = (y >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_add_u32(x0, x1, y0, y1);
        let expected = x.overflowing_add(y);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual, overflowed)
    }

    fn add_small_u32_quickcheck(x: u64, y: u32) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_add_small_u32(x0, x1, y);
        let expected = x.overflowing_add(y as u64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual, overflowed)
    }

    fn sub_u32_quickcheck(x: u64, y: u64) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let y0 = (y & LO32) as u32;
        let y1 = (y >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_sub_u32(x0, x1, y0, y1);
        let expected = x.overflowing_sub(y);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual, overflowed)
    }

    fn sub_small_u32_quickcheck(x: u64, y: u32) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_sub_small_u32(x0, x1, y);
        let expected = x.overflowing_sub(y as u64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual, overflowed)
    }

    fn mul_u32_quickcheck(x: u64, y: u64) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let y0 = (y & LO32) as u32;
        let y1 = (y >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_mul_u32(x0, x1, y0, y1);
        let expected = x.overflowing_mul(y);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual, overflowed)
    }

    fn mul_small_u32_quickcheck(x: u64, y: u32) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_mul_small_u32(x0, x1, y);
        let expected = x.overflowing_mul(y as u64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual, overflowed)
    }

    fn shl_u32_quickcheck(x: u64, n: u32) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let n = (n % 64) as u32;
        let expected = x << n;
        let (lo, hi) = shl_u32(x0, x1, n);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual
    }

    fn shr_u32_quickcheck(x: u64, n: u32) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let n = (n % 64) as u32;
        let expected = x >> n;
        let (lo, hi) = shr_u32(x0, x1, n);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual
    }

    fn swap_bytes_u32_quickcheck(x: u64) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let expected = x.swap_bytes();
        let (lo, hi) = swap_bytes_u32(x0, x1);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual
    }

    fn reverse_bits_u32_quickcheck(x: u64) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let expected = x.reverse_bits();
        let (lo, hi) = reverse_bits_u32(x0, x1);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual
    }

    fn rotate_left_u32_quickcheck(x: u64, n: u32) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let expected = x.rotate_left(n);
        let (lo, hi) = rotate_left_u32(x0, x1, n);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual
    }

    fn rotate_right_u32_quickcheck(x: u64, n: u32) -> bool {
        let x0 = (x & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let expected = x.rotate_right(n);
        let (lo, hi) = rotate_right_u32(x0, x1, n);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual
    }

    fn as_uwide_u32_quickcheck(x: u32) -> bool {
        let expected = x as u64;
        let (lo, hi) = as_uwide_u32(x);
        let hi = hi as u64;
        let actual = (hi << 32) + lo as u64;
        expected == actual
    }

    fn as_iwide_u32_quickcheck(x: i32) -> bool {
        let expected = x as u64;
        let (lo, hi) = as_iwide_u32(x);
        let hi = hi as u64;
        let actual = (hi << 32) + lo as u64;
        expected == actual
    }

    fn as_unarrow_u32_quickcheck(x: u64) -> bool {
        let lo = x as u32;
        let hi = (x >> 32) as u32;
        let expected = x as u32;
        let actual = as_unarrow_u32(lo, hi);
        expected == actual && x as u16 == actual as u16
    }

    fn as_inarrow_u32_quickcheck(x: u64) -> bool {
        let lo = x as u32;
        let hi = (x >> 32) as u32;
        let expected = x as i32;
        let actual = as_inarrow_u32(lo, hi);
        expected == actual && x as i16 == actual as i16
    }

    fn wide_cast_u32_quickcheck(x: u64) -> bool {
        let lo = x as u32;
        let hi = (x >> 32) as u32;
        let expected = (x as u32, hi as i32);
        let actual = wide_cast_u32(lo, hi);
        expected == actual
    }

    fn add_i32_quickcheck(x: i64, y: i64) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let y0 = ((y as u64) & LO32) as u32;
        let y1 = (y >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_add_i32(x0, x1 as i32, y0, y1 as i32);
        let expected = x.overflowing_add(y);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual as i64, overflowed)
    }

    fn add_usmall_i32_quickcheck(x: i64, y: u32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_add_usmall_i32(x0, x1 as i32, y);
        let expected = x.overflowing_add(y as i64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual as i64, overflowed)
    }

    fn add_ismall_i32_quickcheck(x: i64, y: i32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_add_ismall_i32(x0, x1 as i32, y);
        let expected = x.overflowing_add(y as i64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual as i64, overflowed)
    }

    fn sub_i32_quickcheck(x: i64, y: i64) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let y0 = ((y as u64) & LO32) as u32;
        let y1 = (y >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_sub_i32(x0, x1 as i32, y0, y1 as i32);
        let expected = x.overflowing_sub(y);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual as i64, overflowed)
    }

    fn sub_usmall_i32_quickcheck(x: i64, y: u32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_sub_usmall_i32(x0, x1 as i32, y);
        let expected = x.overflowing_sub(y as i64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual as i64, overflowed)
    }

    fn sub_ismall_i32_quickcheck(x: i64, y: i32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_sub_ismall_i32(x0, x1 as i32, y);
        let expected = x.overflowing_sub(y as i64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual as i64, overflowed)
    }

    fn mul_i32_quickcheck(x: i64, y: i64) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let y0 = ((y as u64) & LO32) as u32;
        let y1 = (y >> 32) as u32;
        let (lo, hi) = mul_i32(x0, x1 as i32, y0, y1 as i32);
        let expected = x.wrapping_mul(y);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual as i64
    }

    fn overflowing_mul_i32_quickcheck(x: i64, y: i64) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = (x >> 32) as u32;
        let y0 = ((y as u64) & LO32) as u32;
        let y1 = (y >> 32) as u32;
        let (lo, hi, overflowed) = overflowing_mul_i32(x0, x1 as i32, y0, y1 as i32);
        let expected = x.overflowing_mul(y);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual as i64, overflowed)
    }

    fn mul_usmall_i32_quickcheck(x: i64, y: u32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let (lo, hi) = mul_usmall_i32(x0, x1, y);
        let expected = x.wrapping_mul(y as i64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual as i64
    }

        fn overflowing_mul_usmall_i32_quickcheck(x: i64, y: u32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let (lo, hi, overflowed) = overflowing_mul_usmall_i32(x0, x1, y);
        let expected = x.overflowing_mul(y as i64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual as i64, overflowed)
    }

    fn mul_ismall_i32_quickcheck(x: i64, y: i32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let (lo, hi) = mul_ismall_i32(x0, x1, y);
        let expected = x.wrapping_mul(y as i64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual as i64
    }

    fn overflowing_mul_ismall_i32_quickcheck(x: i64, y: i32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let (lo, hi, overflowed) = overflowing_mul_ismall_i32(x0, x1, y);
        let expected = x.overflowing_mul(y as i64);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == (actual as i64, overflowed)
    }

    fn shl_i32_quickcheck(x: i64, n: u32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let n = (n % 64) as u32;
        let expected = x << n;
        let (lo, hi) = shl_i32(x0, x1, n);
        let actual = lo as i64 + ((hi as u64) << 32) as i64;
        expected == actual
    }

    fn shr_i32_quickcheck(x: i64, n: u32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let n = (n % 64) as u32;
        let expected = x >> n;
        let (lo, hi) = shr_i32(x0, x1, n);
        let actual = lo as i64 + ((hi as u64) << 32) as i64;
        expected == actual
    }

    fn swap_bytes_i32_quickcheck(x: i64) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let expected = x.swap_bytes();
        let (lo, hi) = swap_bytes_i32(x0, x1);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual as i64
    }

    fn reverse_bits_i32_quickcheck(x: i64) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let expected = x.reverse_bits();
        let (lo, hi) = reverse_bits_i32(x0, x1);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual as i64
    }

    fn rotate_left_i32_quickcheck(x: i64, n: u32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let expected = x.rotate_left(n);
        let (lo, hi) = rotate_left_i32(x0, x1, n);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual as i64
    }

    fn rotate_right_i32_quickcheck(x: i64, n: u32) -> bool {
        let x0 = ((x as u64) & LO32) as u32;
        let x1 = ((x as u64) >> 32) as i32;
        let expected = x.rotate_right(n);
        let (lo, hi) = rotate_right_i32(x0, x1, n);
        let actual = lo as u64 + ((hi as u64) << 32);
        expected == actual as i64
    }

    fn as_uwide_i32_quickcheck(x: u32) -> bool {
        let expected = x as i64;
        let (lo, hi) = as_uwide_i32(x);
        let hi = (hi as u32) as u64;
        let unsigned = (hi << 32) + lo as u64;
        let actual = unsigned as i64;
        expected == actual
    }

    fn as_iwide_i32_quickcheck(x: i32) -> bool {
        let expected = x as i64;
        let (lo, hi) = as_iwide_i32(x);
        let hi = (hi as u32) as u64;
        let unsigned = (hi << 32) + lo as u64;
        let actual = unsigned as i64;
        expected == actual
    }

    fn as_unarrow_i32_quickcheck(x: u64) -> bool {
        let lo = x as u32;
        let hi = (x >> 32) as i32;
        let expected = x as u32;
        let actual = as_unarrow_i32(lo, hi);
        expected == actual && x as u16 == actual as u16
    }

    fn as_inarrow_i32_quickcheck(x: i64) -> bool {
        let lo = x as u32;
        let hi = (x >> 32) as i32;
        let expected = x as i32;
        let actual = as_inarrow_i32(lo, hi);
        expected == actual && x as i16 == actual as i16
    }

    fn wide_cast_i32_quickcheck(x: i64) -> bool {
        let lo = x as u32;
        let hi = (x >> 32) as i32;
        let expected = (x as u32, hi as u32);
        let actual = wide_cast_i32(lo, hi);
        expected == actual
    }
}
