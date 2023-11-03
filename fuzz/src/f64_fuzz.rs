#![cfg(test)]

use crate::sf64::{fuzz_test_op, fuzz_test_op_2, fuzz_test_op_2_other};
use softfloat::F64;

mod basic_tests {
    use super::*;
    #[test]
    fn fuzz_add() {
        fuzz_test_op_2(
            F64::add,
            crate::compiler_builtins::add,
            crate::Argument::First,
            None,
            Some("add"),
        );
        fuzz_test_op_2(
            F64::add,
            crate::compiler_builtins::add,
            crate::Argument::Second,
            None,
            Some("add"),
        );
    }

    #[test]
    fn fuzz_sub() {
        fuzz_test_op_2(
            F64::sub,
            crate::compiler_builtins::sub,
            crate::Argument::First,
            None,
            Some("sub"),
        );
        fuzz_test_op_2(
            F64::sub,
            crate::compiler_builtins::sub,
            crate::Argument::Second,
            None,
            Some("sub"),
        );
    }

    #[test]
    fn fuzz_div() {
        fuzz_test_op_2(
            F64::div,
            crate::compiler_builtins::div64,
            crate::Argument::First,
            None,
            Some("div"),
        );
        fuzz_test_op_2(
            F64::div,
            crate::compiler_builtins::div64,
            crate::Argument::Second,
            None,
            Some("div"),
        );
    }

    #[test]
    fn fuzz_mul() {
        fuzz_test_op_2(
            F64::mul,
            crate::compiler_builtins::mul,
            crate::Argument::First,
            None,
            Some("mul"),
        );
        fuzz_test_op_2(
            F64::mul,
            crate::compiler_builtins::mul,
            crate::Argument::Second,
            None,
            Some("mul"),
        );
    }

    #[test]
    fn fuzz_pow() {
        fuzz_test_op_2_other(F64::powi, crate::compiler_builtins::powi, None, Some("pow"))
    }

    #[test]
    fn fuzz_round() {
        fuzz_test_op(F64::round, f64::round, None, Some("round"))
    }

    #[test]
    fn fuzz_trunc() {
        fuzz_test_op(F64::trunc, f64::trunc, None, Some("trunc"));
    }

    #[test]
    fn fuzz_min() {
        fuzz_test_op_2(
            F64::min,
            f64::min,
            crate::Argument::First,
            None,
            Some("min"),
        );
        fuzz_test_op_2(
            F64::min,
            f64::min,
            crate::Argument::Second,
            None,
            Some("min"),
        );
    }

    #[test]
    fn fuzz_max() {
        fuzz_test_op_2(
            F64::max,
            f64::max,
            crate::Argument::First,
            None,
            Some("max"),
        );
        fuzz_test_op_2(
            F64::max,
            f64::max,
            crate::Argument::Second,
            None,
            Some("max"),
        );
    }
}

mod libm_tests {
    use super::*;

    #[test]
    fn fuzz_sqrt() {
        fuzz_test_op(F64::sqrt, libm::sqrt, None, Some("sqrt"))
    }

    #[test]
    fn fuzz_copysign() {
        fuzz_test_op_2(
            F64::copysign,
            libm::copysign,
            crate::Argument::First,
            None,
            Some("copysign"),
        );
        fuzz_test_op_2(
            F64::copysign,
            libm::copysign,
            crate::Argument::Second,
            None,
            Some("copysign"),
        );
    }

    #[test]
    fn fuzz_floor() {
        fuzz_test_op(F64::floor, libm::floor, None, Some("floor"))
    }

    #[test]
    fn fuzz_sin() {
        // cannot remove all instance of hard-float usage in libm
        fuzz_test_op(F64::sin, libm::sin, Some(1e-6), Some("sin"))
    }

    #[test]
    fn fuzz_cos() {
        // cannot remove all instance of hard-float usage in libm, so
        fuzz_test_op(F64::cos, libm::cos, Some(1e-6), Some("cos"))
    }

    #[test]
    fn fuzz_ln() {
        fuzz_test_op(F64::ln, libm::log, None, Some("ln"));
    }

    #[test]
    fn fuzz_exp() {
        fuzz_test_op(F64::exp, libm::exp, None, Some("exp"));
    }
}
