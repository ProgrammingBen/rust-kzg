#[cfg(test)]
pub mod poly_tests {
    use kzg_bench::tests::poly::*;
    use mcl_rust::data_types::fr::Fr;
    use mcl_rust::kzg10::Polynomial;
    use mcl_rust::mcl_methods::init;
    use mcl_rust::CurveType;

    #[test]
    fn create_poly_of_length_ten_() {
        assert!(init(CurveType::BLS12_381));
        create_poly_of_length_ten::<Fr, Polynomial>();
    }

    #[test]
    fn poly_eval_check_() {
        assert!(init(CurveType::BLS12_381));
        poly_eval_check::<Fr, Polynomial>();
    }

    #[test]
    fn poly_eval_0_check_() {
        assert!(init(CurveType::BLS12_381));
        poly_eval_0_check::<Fr, Polynomial>();
    }

    #[test]
    fn poly_eval_nil_check_() {
        assert!(init(CurveType::BLS12_381));
        poly_eval_nil_check::<Fr, Polynomial>();
    }

    #[test]
    fn poly_inverse_simple_0_() {
        assert!(init(CurveType::BLS12_381));
        poly_inverse_simple_0::<Fr, Polynomial>();
    }

    #[test]
    fn poly_inverse_simple_1_() {
        assert!(init(CurveType::BLS12_381));
        poly_inverse_simple_1::<Fr, Polynomial>();
    }
}
