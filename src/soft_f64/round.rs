use super::SoftF64;

pub(crate) const fn round(x: SoftF64) -> SoftF64 {
    SoftF64::trunc(x.add(SoftF64::copysign(
        f64!(0.5).sub(f64!(0.25).mul(f64!(f64::EPSILON))),
        x,
    )))
}

#[cfg(test)]
mod tests {
    use super::SoftF64;

    #[test]
    fn negative_zero() {
        assert_eq!(SoftF64::round(f64!(-0.0)).to_bits(), f64!(-0.0).to_bits());
    }

    #[test]
    fn sanity_check() {
        assert_eq!((f64!(-1.0)).round(), f64!(-1.0));
        assert_eq!((f64!(2.8)).round(), f64!(3.0));
        assert_eq!((f64!(-0.5)).round(), f64!(-1.0));
        assert_eq!((f64!(0.5)).round(), f64!(1.0));
        assert_eq!((f64!(-1.5)).round(), f64!(-2.0));
        assert_eq!((f64!(1.5)).round(), f64!(2.0));
    }
}
