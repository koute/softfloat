#![cfg(test)]

use crate::sf32::{fuzz_test_op, fuzz_test_op_2, fuzz_test_op_2_other};
use nanorand::Rng;
use softfloat::F32;

mod basic_tests {
    use super::*;

    #[test]
    fn fuzz_add() {
        fuzz_test_op_2(
            F32::add,
            crate::compiler_builtins::add,
            crate::Argument::First,
            None,
            Some("add"),
        );
        fuzz_test_op_2(
            F32::add,
            crate::compiler_builtins::add,
            crate::Argument::Second,
            None,
            Some("add"),
        );
    }

    #[test]
    fn fuzz_sub() {
        fuzz_test_op_2(
            F32::sub,
            crate::compiler_builtins::sub,
            crate::Argument::First,
            None,
            Some("sub"),
        );
        fuzz_test_op_2(
            F32::sub,
            crate::compiler_builtins::sub,
            crate::Argument::Second,
            None,
            Some("sub"),
        );
    }

    #[test]
    fn fuzz_div() {
        fuzz_test_op_2(
            F32::div,
            crate::compiler_builtins::div32,
            crate::Argument::First,
            None,
            Some("div"),
        );
        fuzz_test_op_2(
            F32::div,
            crate::compiler_builtins::div32,
            crate::Argument::Second,
            None,
            Some("div"),
        );
    }

    #[test]
    fn fuzz_mul() {
        fuzz_test_op_2(
            F32::mul,
            crate::compiler_builtins::mul,
            crate::Argument::First,
            None,
            Some("mul"),
        );
        fuzz_test_op_2(
            F32::mul,
            crate::compiler_builtins::mul,
            crate::Argument::Second,
            None,
            Some("mul"),
        );
    }

    #[test]
    fn fuzz_pow() {
        // TODO move this to a new test generator
        let mut rng = nanorand::WyRand::new();
        for i in i32::MIN..i32::MAX {
            let fl = F32::from_bits(rng.generate::<u32>());
            let res1 = fl.powi(i).to_native_f32();
            let res2 = crate::compiler_builtins::powif(fl.to_native_f32(), i);
            if !match (res1, res2) {
                (a, b) if a.is_nan() && b.is_nan() => true,
                (a, b) => a == b,
            } {
                eprintln!("failed: base = {}, pow = {}", fl.to_native_f32(), i);
                eprintln!("res: soft = {}, ref = {}", res1, res2);
                panic!()
            }
        }
        fuzz_test_op_2_other(
            F32::powi,
            crate::compiler_builtins::powif,
            None,
            Some("pow"),
        )
    }

    #[test]
    fn fuzz_round() {
        fuzz_test_op(F32::round, f32::round, None, Some("round"))
    }

    #[test]
    fn fuzz_trunc() {
        fuzz_test_op(F32::trunc, f32::trunc, None, Some("trunc"));
    }
}

mod libm_tests {
    use super::*;

    #[test]
    fn fuzz_sqrt() {
        fuzz_test_op(F32::sqrt, libm::sqrtf, None, Some("sqrt"))
    }

    #[test]
    fn fuzz_copysign() {
        fuzz_test_op_2(
            F32::copysign,
            libm::copysignf,
            crate::Argument::First,
            None,
            Some("copysign"),
        );
        fuzz_test_op_2(
            F32::copysign,
            libm::copysignf,
            crate::Argument::Second,
            None,
            Some("copysign"),
        );
    }

    #[test]
    fn fuzz_floor() {
        fuzz_test_op(F32::floor, libm::floorf, None, Some("floor"))
    }

    #[test]
    fn fuzz_sin() {
        fuzz_test_op(F32::sin, libm::sinf, None, Some("sin"))
    }

    #[test]
    fn fuzz_cos() {
        fuzz_test_op(F32::cos, libm::cosf, None, Some("cos"))
    }
}
