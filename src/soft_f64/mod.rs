use crate::soft_f32::F32;

pub(crate) mod helpers;

pub mod add;
pub mod cmp;
pub mod copysign;
pub mod cos;
pub mod div;
pub mod exp;
pub mod floor;
pub mod log;
pub mod mul;
pub mod pow;
pub mod round;
pub mod sin;
pub mod sqrt;
pub mod trunc;

#[derive(Default, Copy, Clone, Debug)]
#[repr(transparent)]
struct Bits64(u64);

#[derive(Default, Copy, Clone, Debug)]
#[repr(transparent)]
pub struct F64(Bits64);

impl F64 {
    pub const fn from_native_f64(a: f64) -> Self {
        Self(unsafe { core::mem::transmute(a) })
    }

    pub const fn to_native_f64(self) -> f64 {
        unsafe { core::mem::transmute(self.0) }
    }

    pub const fn from_f32(a: F32) -> Self {
        a.to_f64()
    }

    pub const fn to_f32(self) -> F32 {
        F32::from_f64(self)
    }

    pub const fn from_i32(a: i32) -> Self {
        crate::conv::i32_to_f64(a)
    }

    pub const fn to_i32(self) -> i32 {
        crate::conv::f64_to_i32(self)
    }

    pub const fn from_bits(a: u64) -> Self {
        Self(Bits64(a))
    }

    pub const fn to_bits(self) -> u64 {
        self.0 .0
    }

    pub const fn add(self, rhs: Self) -> Self {
        add::add(self, rhs)
    }

    pub const fn mul(self, rhs: Self) -> Self {
        mul::mul(self, rhs)
    }

    pub const fn div(self, rhs: Self) -> Self {
        div::div(self, rhs)
    }

    pub const fn cmp(self, rhs: Self) -> Option<core::cmp::Ordering> {
        cmp::cmp(self, rhs)
    }

    pub const fn neg(self) -> Self {
        Self::from_repr(self.repr() ^ Self::SIGN_MASK)
    }

    pub const fn sub(self, rhs: Self) -> Self {
        self.add(rhs.neg())
    }

    pub const fn sqrt(self) -> Self {
        sqrt::sqrt(self)
    }

    pub const fn powi(self, n: i32) -> Self {
        pow::pow(self, n)
    }

    pub const fn copysign(self, other: Self) -> Self {
        copysign::copysign(self, other)
    }

    pub const fn trunc(self) -> Self {
        trunc::trunc(self)
    }

    pub const fn round(self) -> Self {
        round::round(self)
    }

    pub const fn floor(self) -> Self {
        floor::floor(self)
    }

    pub const fn sin(self) -> Self {
        sin::sin(self)
    }

    pub const fn cos(self) -> Self {
        cos::cos(self)
    }

    pub const fn is_nan(self) -> bool {
        !matches!(self.cmp(self), Some(core::cmp::Ordering::Equal))
    }

    pub const fn max(self, other: Self) -> Self {
        let cond = self.is_nan() || matches!(self.cmp(other), Some(core::cmp::Ordering::Less));
        (if cond { other } else { self }).mul(Self::ONE)
    }

    pub const fn min(self, other: Self) -> Self {
        let cond = other.is_nan() || matches!(self.cmp(other), Some(core::cmp::Ordering::Less));
        (if cond { self } else { other }).mul(Self::ONE)
    }

    pub const fn exp(self) -> Self {
        exp::exp(self)
    }

    pub const fn ln(self) -> Self {
        log::log(self)
    }

    pub const fn is_sign_negative(self) -> bool {
        self.to_bits() & 0x8000_0000_0000_0000 != 0
    }
}

type SelfInt = u64;
type SelfSignedInt = i64;
type SelfExpInt = i16;

#[allow(unused)]
impl F64 {
    const ZERO: Self = f64!(0.0);
    const ONE: Self = f64!(1.0);
    pub(crate) const BITS: u32 = 64;
    pub(crate) const SIGNIFICAND_BITS: u32 = 52;
    pub(crate) const EXPONENT_BITS: u32 = Self::BITS - Self::SIGNIFICAND_BITS - 1;
    pub(crate) const EXPONENT_MAX: u32 = (1 << Self::EXPONENT_BITS) - 1;
    pub(crate) const EXPONENT_BIAS: u32 = Self::EXPONENT_MAX >> 1;
    pub(crate) const SIGN_MASK: SelfInt = 1 << (Self::BITS - 1);
    pub(crate) const SIGNIFICAND_MASK: SelfInt = (1 << Self::SIGNIFICAND_BITS) - 1;
    pub(crate) const IMPLICIT_BIT: SelfInt = 1 << Self::SIGNIFICAND_BITS;
    pub(crate) const EXPONENT_MASK: SelfInt = !(Self::SIGN_MASK | Self::SIGNIFICAND_MASK);

    pub(crate) const fn repr(self) -> SelfInt {
        self.to_bits()
    }
    const fn signed_repr(self) -> SelfSignedInt {
        self.to_bits() as SelfSignedInt
    }
    const fn sign(self) -> bool {
        self.signed_repr() < 0
    }
    const fn exp2(self) -> SelfExpInt {
        ((self.to_bits() & Self::EXPONENT_MASK) >> Self::SIGNIFICAND_BITS) as SelfExpInt
    }
    const fn frac(self) -> SelfInt {
        self.to_bits() & Self::SIGNIFICAND_MASK
    }
    const fn imp_frac(self) -> SelfInt {
        self.frac() | Self::IMPLICIT_BIT
    }
    pub(crate) const fn from_repr(a: SelfInt) -> Self {
        Self::from_bits(a)
    }
    const fn from_parts(sign: bool, exponent: SelfInt, significand: SelfInt) -> Self {
        Self::from_repr(
            ((sign as SelfInt) << (Self::BITS - 1))
                | ((exponent << Self::SIGNIFICAND_BITS) & Self::EXPONENT_MASK)
                | (significand & Self::SIGNIFICAND_MASK),
        )
    }
    const fn normalize(significand: SelfInt) -> (i32, SelfInt) {
        let shift = significand
            .leading_zeros()
            .wrapping_sub((1u64 << Self::SIGNIFICAND_BITS).leading_zeros());
        (
            1i32.wrapping_sub(shift as i32),
            significand << shift as SelfInt,
        )
    }
    const fn is_subnormal(self) -> bool {
        (self.repr() & Self::EXPONENT_MASK) == 0
    }

    const fn scalbn(self, n: i32) -> F64 {
        helpers::scalbn(self, n)
    }
}

const fn u128_lo(x: u128) -> u64 {
    x as u64
}

const fn u128_hi(x: u128) -> u64 {
    (x >> 64) as u64
}

const fn u64_widen_mul(a: u64, b: u64) -> (u64, u64) {
    let x = u128::wrapping_mul(a as _, b as _);
    (u128_lo(x), u128_hi(x))
}
