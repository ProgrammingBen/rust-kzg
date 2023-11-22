use blst::{
    blst_fp, blst_p1, blst_p1_add_or_double, blst_p1_affine, blst_p1_double, blst_p1_from_affine,
    blst_p1_generator, blst_p1_to_affine,
};

pub const N_EXP: usize = 10;
pub const N_POINTS: usize = 1 << N_EXP;
pub const H_BGMW95: usize = 22;
pub const H_LEN_SCALAR: usize = 20;
pub const EXPONENT_OF_Q: usize = 13;
pub const Q_RADIX: usize = 1 << EXPONENT_OF_Q;
pub const EXPONENT_OF_Q_BGMW95: usize = 12;
pub const Q_RADIX_PIPPENGER_VARIANT: usize = 1 << EXPONENT_OF_Q_BGMW95;
// pub fn pippenger_variant_BGMW95(scalars_array: *const *const byte) -> blst_p1_affine {
//     let mut ret_qhalf_expr: [i32; h_BGMW95];
//     let mut npoints: usize = N_POINTS*h_BGMW95;

//     let mut scalars = vec![blst_scalar::default(); N_POINTS];

//     let mut booth_signs: u8 = vec![0, N_POINTS];

//     let mut points_ptr = vec![blst_p1_affine::default(); N_POINTS];

//     if (N_EXP == 13 || N_EXP == 14 || N_EXP == 16 || N_EXP == 17){

//         let mut tt: u64 = u64(1) << 62;
//         for i in 0..N_POINTS{
//             let mut aa;

//             let mut condition: bool = aa.data[3] > tt;
//             if(condition){
//                 aa == r_GROUP_ORDER - aa;
//             }

//             trans_uint
//         }

//         }
//     }
// }

// pub fn trans_uint256_t_to_qhalf_expr(&ret_qhalf_expr: [i32; h_BGMW95], &a: *const *const byte){

// }

pub fn single_scalar_multiplication(mut scalar: usize, q: blst_p1_affine) -> blst_p1_affine {
    let mut ret: blst_p1_affine = blst_p1_affine::default();
    let mut inf: blst_p1 = blst_p1 {
        x: blst_fp {
            l: [0, 1, 0, 0, 0, 0],
        },
        y: blst_fp {
            l: [0, 0, 0, 0, 0, 0],
        },
        z: blst_fp {
            l: [0, 0, 0, 0, 0, 0],
        },
    };
    let mut xyz_q: blst_p1 = blst_p1::default();
    unsafe {
        blst_p1_from_affine(&mut xyz_q, &q);
        while scalar > 0 {
            if scalar & 1 != 0 {
                blst_p1_add_or_double(&mut inf, &inf, &xyz_q);
            }

            blst_p1_add_or_double(&mut xyz_q, &xyz_q, &xyz_q);
            scalar = scalar >> 1
        }
        blst_p1_to_affine(&mut ret, &inf);
        return ret;
    };
}

pub fn init_pippenger_bgmw(
    table: &mut [blst_p1_affine],
    points: &[blst_p1_affine],
) -> Vec<blst_p1_affine> {
    // bmw95 list
    let mut precomputation_points_list_bgmw95 =
        vec![blst_p1_affine::default(); H_BGMW95 * N_POINTS];

    if Q_RADIX == Q_RADIX_PIPPENGER_VARIANT {
        // 3nh list
        let mut precomputation_points_list_3nh =
            vec![blst_p1_affine::default(); 3 * N_POINTS * H_LEN_SCALAR];

        for i in 0..points.len() {
            let mut tmp_p_affine = points[i];
            for j in 0..H_LEN_SCALAR {
                for m in 1..3 {
                    let idx_i_j_m: usize = 3 * (i * H_LEN_SCALAR + j) + m - 1;
                    if m == 1 {
                        precomputation_points_list_3nh[idx_i_j_m] = tmp_p_affine;
                    } else {
                        precomputation_points_list_3nh[idx_i_j_m] =
                            single_scalar_multiplication(m, tmp_p_affine);
                    }
                    tmp_p_affine = single_scalar_multiplication(Q_RADIX, tmp_p_affine);
                }
            }
        }

        for i in 0..N_POINTS {
            for j in 0..H_BGMW95 {
                let idx = i * H_BGMW95 + j;
                precomputation_points_list_bgmw95[idx] = precomputation_points_list_3nh[3 * idx];
            }
        }
    } else {
        for i in 0..N_POINTS {
            let mut tmp_p_affine = points[i];
            for j in 0..H_BGMW95 {
                let idx = i * H_BGMW95 + j;
                precomputation_points_list_bgmw95[idx] = tmp_p_affine;
                tmp_p_affine =
                    single_scalar_multiplication(Q_RADIX_PIPPENGER_VARIANT, tmp_p_affine);
            }
        }
    }

    return precomputation_points_list_bgmw95;
}
