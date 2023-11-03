//! # Rust float-point in constant context
//!
//! work in `stable`:
//! ```
//! # use const_soft_float::soft_f32::SoftF32;
//! const fn const_f32_add(a: f32, b: f32) -> f32 {
//!     SoftF32::from_native_f32(a).add(SoftF32::from_native_f32(b)).to_native_f32()
//! }
//! ```

#![no_std]

#[macro_export]
macro_rules! f32 {
    ($value:expr) => {{
        const C: $crate::soft_f32::SoftF32 = { $crate::soft_f32::SoftF32::from_native_f32($value) };
        C
    }};
}

#[macro_export]
macro_rules! f64 {
    ($value:expr) => {{
        const C: $crate::soft_f64::SoftF64 = { $crate::soft_f64::SoftF64::from_native_f64($value) };
        C
    }};
}

pub mod soft_f32;
pub mod soft_f64;

mod conv;

const fn abs_diff(a: i32, b: i32) -> u32 {
    a.wrapping_sub(b).wrapping_abs() as u32
}

macro_rules! impl_traits {
    ($ty:ty, $native_ty:ty, $from_native:ident) => {
        impl From<$native_ty> for $ty {
            fn from(value: $native_ty) -> Self {
                Self::$from_native(value)
            }
        }

        impl PartialEq<Self> for $ty {
            fn eq(&self, other: &Self) -> bool {
                match self.cmp(*other) {
                    Some(core::cmp::Ordering::Equal) => true,
                    _ => false,
                }
            }
        }

        impl PartialOrd for $ty {
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                self.cmp(*other)
            }
        }

        impl core::ops::Add for $ty {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                Self::add(self, rhs)
            }
        }

        impl core::ops::Sub for $ty {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self::Output {
                Self::sub(self, rhs)
            }
        }

        impl core::ops::Mul for $ty {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self::Output {
                Self::mul(self, rhs)
            }
        }

        impl core::ops::Div for $ty {
            type Output = Self;

            fn div(self, rhs: Self) -> Self::Output {
                Self::div(self, rhs)
            }
        }

        impl core::ops::AddAssign for $ty {
            fn add_assign(&mut self, rhs: Self) {
                *self = *self + rhs;
            }
        }

        impl core::ops::SubAssign for $ty {
            fn sub_assign(&mut self, rhs: Self) {
                *self = *self - rhs;
            }
        }
    };
}

impl_traits!(crate::soft_f32::SoftF32, f32, from_native_f32);
impl_traits!(crate::soft_f64::SoftF64, f64, from_native_f64);

#[cfg(test)]
mod tests {
    use crate::soft_f32::SoftF32;
    use crate::soft_f64::SoftF64;

    const RANGE: core::ops::Range<i32> = -1000..1000;
    const F32_FACTOR: f32 = 10.0;
    const F64_FACTOR: f64 = 1000.0;

    #[test]
    fn f32_add() {
        for a in RANGE {
            let a = a as f32 * F32_FACTOR;
            for b in RANGE {
                let b = b as f32 * F32_FACTOR;
                assert_eq!(
                    SoftF32::from_native_f32(a)
                        .add(SoftF32::from_native_f32(b))
                        .to_native_f32(),
                    a + b
                );
            }
        }
    }

    #[test]
    fn f32_sub() {
        for a in RANGE {
            let a = a as f32 * F32_FACTOR;
            for b in RANGE {
                let b = b as f32 * F32_FACTOR;
                assert_eq!(
                    SoftF32::from_native_f32(a)
                        .sub(SoftF32::from_native_f32(b))
                        .to_native_f32(),
                    a - b
                );
            }
        }
    }

    #[test]
    fn f32_mul() {
        for a in RANGE {
            let a = a as f32 * F32_FACTOR;
            for b in RANGE {
                let b = b as f32 * F32_FACTOR;
                assert_eq!(
                    SoftF32::from_native_f32(a)
                        .mul(SoftF32::from_native_f32(b))
                        .to_native_f32(),
                    a * b
                );
            }
        }
    }

    #[test]
    fn f32_div() {
        for a in RANGE {
            let a = a as f32 * F32_FACTOR;
            for b in RANGE {
                let b = b as f32 * F32_FACTOR;
                let x = SoftF32::from_native_f32(a)
                    .div(SoftF32::from_native_f32(b))
                    .to_native_f32();
                let y = a / b;
                assert!(x == y || x.is_nan() && y.is_nan())
            }
        }
    }

    #[test]
    fn f64_add() {
        for a in RANGE {
            let a = a as f64 * F64_FACTOR;
            for b in RANGE {
                let b = b as f64 * F64_FACTOR;
                assert_eq!(
                    SoftF64::from_native_f64(a)
                        .sub(SoftF64::from_native_f64(b))
                        .to_native_f64(),
                    a - b
                );
            }
        }
    }

    #[test]
    fn f64_sub() {
        for a in RANGE {
            let a = a as f64 * F64_FACTOR;
            for b in RANGE {
                let b = b as f64 * F64_FACTOR;
                assert_eq!(
                    SoftF64::from_native_f64(a)
                        .sub(SoftF64::from_native_f64(b))
                        .to_native_f64(),
                    a - b
                );
            }
        }
    }

    #[test]
    fn f64_mul() {
        for a in RANGE {
            let a = a as f64 * F64_FACTOR;
            for b in RANGE {
                let b = b as f64 * F64_FACTOR;
                assert_eq!(
                    SoftF64::from_native_f64(a)
                        .mul(SoftF64::from_native_f64(b))
                        .to_native_f64(),
                    a * b
                );
            }
        }
    }

    #[test]
    fn f64_div() {
        for a in RANGE {
            let a = a as f64 * F64_FACTOR;
            for b in RANGE {
                let b = b as f64 * F64_FACTOR;
                let x = SoftF64::from_native_f64(a)
                    .div(SoftF64::from_native_f64(b))
                    .to_native_f64();
                let y = a / b;
                assert!(x == y || x.is_nan() && y.is_nan())
            }
        }
    }
}
