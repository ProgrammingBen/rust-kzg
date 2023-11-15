use core::{mem::size_of, ptr::null_mut};

use blst::{
    blst_fp, blst_p1, blst_p1_add, blst_p1_affine, blst_p1_double, blst_p1_from_affine,
    blst_p1_mult, blst_p1s_mult_wbits, blst_p1s_mult_wbits_precompute, byte, limb_t,
};

fn pippenger_window_size(mut npoints: usize) -> usize {
    let mut wbits = 0usize;

    loop {
        npoints >>= 1;
        if npoints == 0 {
            break;
        }
        wbits += 1;
    }

    if wbits > 12 {
        wbits - 3
    } else if wbits > 4 {
        wbits - 2
    } else if wbits != 0 {
        2
    } else {
        1
    }
}

fn is_zero(val: limb_t) -> limb_t {
    (!val & (val.wrapping_sub(1))) >> (limb_t::BITS - 1)
}

fn booth_encode(wval: limb_t, sz: usize) -> limb_t {
    let mask = (0 as limb_t).wrapping_sub(wval >> sz);

    let wval = (wval + 1) >> 1;
    (wval ^ mask).wrapping_sub(mask)
}

#[inline(always)]
unsafe fn vec_zero(ret: *mut limb_t, mut num: usize) {
    num /= size_of::<usize>();

    for i in 0..num {
        *ret.add(i) = 0;
    }
}

unsafe fn get_wval_limb(mut d: *const byte, off: usize, bits: usize) -> limb_t {
    let mut top = (off + bits - 1) / 8;
    let mut mask = (0 as limb_t).wrapping_sub(1);

    d = d.wrapping_add(off / 8);

    top = top.wrapping_sub((off / 8).wrapping_sub(1));

    let mut ret: limb_t = 0;
    let mut i: usize = 0;
    loop {
        ret |= (*d as limb_t & mask) << (8 * i);
        mask =
            (0 as limb_t).wrapping_sub(((i + 1).wrapping_sub(top) >> (usize::BITS - 1)) as limb_t);
        i += 1;
        d = d.wrapping_add((1 & mask).try_into().unwrap());
        if i >= 4 {
            break ret >> (off % 8);
        }
    }
}

#[inline(always)]
unsafe fn vec_is_zero(a: *const byte, num: usize) -> limb_t {
    let ap = a as *const limb_t;
    let num = num / size_of::<limb_t>();

    let mut acc: limb_t = 0;
    for i in 0..num {
        acc |= *ap.wrapping_add(i);
    }

    is_zero(acc)
}

#[inline(always)]
unsafe fn vec_copy(ret: *mut u8, a: *const u8, num: usize) {
    let rp = ret as *mut limb_t;
    let ap = a as *const limb_t;

    let num = num / size_of::<limb_t>();

    for i in 0..num {
        *rp.wrapping_add(i) = *ap.wrapping_add(i);
    }
}

const BLS12_381_RX_P: blst_fp = blst_fp {
    l: [
        8505329371266088957,
        17002214543764226050,
        6865905132761471162,
        8632934651105793861,
        6631298214892334189,
        1582556514881692819,
    ],
};

unsafe fn p1_dadd_affine(
    p3: *mut P1XYZZ,
    p1: *const P1XYZZ,
    p2: *const blst_p1_affine,
    subtract: limb_t,
) {
    // POINTonE1xyzz *p3, const POINTonE1xyzz *p1, const POINTonE1_affine *p2, bool_t subtract
    // vec384 P, R;

    // if (vec_is_zero(p2, sizeof(*p2)))
    if vec_is_zero(p2 as *const u8, size_of::<blst_p1_affine>()) != 0 {
        // vec_copy(p3, p1, sizeof(*p3));
        vec_copy(p3 as *mut u8, p1 as *const u8, size_of::<P1XYZZ>());
        return;
    // else if (vec_is_zero(p1->ZZZ, 2 * sizeof(p1->ZZZ)))
    } else if vec_is_zero(
        &(*p1).zzz as *const blst_fp as *const u8,
        2 * size_of::<blst_fp>(),
    ) != 0
    {
        // vec_copy(p3->X, p2->X, 2 * sizeof(p3->X));
        vec_copy(
            &mut ((*p3).x) as *mut blst_fp as *mut u8,
            &((*p2).x) as *const blst_fp as *const u8,
            2 * size_of::<blst_fp>(),
        );
        // cneg_fp(p3->ZZZ, BLS12_381_Rx.p, subtract);
        blst::blst_fp_cneg(&mut (*p3).zzz, &BLS12_381_RX_P, subtract != 0);
        // vec_copy(p3->ZZ, BLS12_381_Rx.p, sizeof(p3->ZZ));
        vec_copy(
            &mut ((*p3).zz) as *mut blst_fp as *mut u8,
            &BLS12_381_RX_P as *const blst_fp as *const u8,
            size_of::<blst_fp>(),
        );
        // return
        return;
    }

    let mut p = blst_fp::default();
    let mut r = blst_fp::default();

    // mul_fp(P, p2->X, p1->ZZ);
    blst::blst_fp_mul(&mut p, &(*p2).x, &(*p1).zz);
    // mul_fp(R, p2->Y, p1->ZZZ);
    blst::blst_fp_mul(&mut r, &(*p2).y, &(*p1).zzz);
    // cneg_fp(R, R, subtract);
    blst::blst_fp_cneg(&mut r, &r, subtract != 0);
    // sub_fp(P, P, p1->X);
    blst::blst_fp_sub(&mut p, &p, &(*p1).x);
    // sub_fp(R, R, p1->Y);
    blst::blst_fp_sub(&mut r, &r, &(*p1).y);
    // if (!vec_is_zero(P, sizeof(P)))
    if vec_is_zero(&p as *const blst_fp as *const u8, size_of::<blst_fp>()) == 0 {
        // vec384 PP, PPP, Q;
        let mut pp = blst_fp::default();
        let mut ppp = blst_fp::default();
        let mut q = blst_fp::default();
        // sqr_fp(PP, P);
        blst::blst_fp_sqr(&mut pp, &p);
        // mul_fp(PPP, PP, P);
        blst::blst_fp_mul(&mut ppp, &pp, &p);
        // mul_fp(Q, p1->X, PP);
        blst::blst_fp_mul(&mut q, &(*p1).x, &pp);
        // sqr_fp(p3->X, R);
        blst::blst_fp_sqr(&mut (*p3).x, &r);
        // add_fp(P, Q, Q);
        blst::blst_fp_add(&mut p, &q, &q);
        // sub_fp(p3->X, p3->X, PPP);
        blst::blst_fp_sub(&mut (*p3).x, &(*p3).x, &ppp);
        // sub_fp(p3->X, p3->X, P);
        blst::blst_fp_sub(&mut (*p3).x, &(*p3).x, &p);
        // sub_fp(Q, Q, p3->X);
        blst::blst_fp_sub(&mut q, &q, &(*p3).x);
        // mul_fp(Q, Q, R);
        blst::blst_fp_mul(&mut q, &q, &r);
        // mul_fp(p3->Y, p1->Y, PPP);
        blst::blst_fp_mul(&mut (*p3).y, &(*p1).y, &ppp);
        // sub_fp(p3->Y, Q, p3->Y);
        blst::blst_fp_sub(&mut (*p3).y, &q, &(*p3).y);
        // mul_fp(p3->ZZ, p1->ZZ, PP);
        blst::blst_fp_mul(&mut (*p3).zz, &(*p1).zz, &pp);
        // mul_fp(p3->ZZZ, p1->ZZZ, PPP);
        blst::blst_fp_mul(&mut (*p3).zzz, &(*p1).zzz, &ppp);
    // else if (vec_is_zero(R, sizeof(R)))
    } else if vec_is_zero(&r as *const blst_fp as *const u8, size_of::<blst_fp>()) != 0 {
        // vec384 U, S, M;
        let mut u = blst_fp::default();
        let mut s = blst_fp::default();
        let mut m = blst_fp::default();
        // add_fp(U, p2->Y, p2->Y);
        blst::blst_fp_add(&mut u, &(*p2).y, &(*p2).y);
        // sqr_fp(p3->ZZ, U);
        blst::blst_fp_sqr(&mut (*p3).zz, &u);
        // mul_fp(p3->ZZZ, p3->ZZ, U);
        blst::blst_fp_mul(&mut (*p3).zzz, &(*p3).zz, &u);
        // mul_fp(S, p2->X, p3->ZZ);
        blst::blst_fp_mul(&mut s, &(*p2).x, &(*p3).zz);
        // sqr_fp(M, p2->X);
        blst::blst_fp_sqr(&mut m, &(*p2).x);
        // mul_by_3_fp(M, M);
        blst::blst_fp_mul_by_3(&mut m, &m);
        // sqr_fp(p3->X, M);
        blst::blst_fp_sqr(&mut (*p3).x, &m);
        // add_fp(U, S, S);
        blst::blst_fp_add(&mut u, &s, &s);
        // sub_fp(p3->X, p3->X, U);
        blst::blst_fp_sub(&mut (*p3).x, &(*p3).x, &u);
        // mul_fp(p3->Y, p3->ZZZ, p2->Y);
        blst::blst_fp_mul(&mut (*p3).y, &(*p3).zzz, &(*p2).y);
        // sub_fp(S, S, p3->X);
        blst::blst_fp_sub(&mut s, &s, &(*p3).x);
        // mul_fp(S, S, M);
        blst::blst_fp_mul(&mut s, &s, &m);
        // sub_fp(p3->Y, S, p3->Y);
        blst::blst_fp_sub(&mut (*p3).y, &s, &(*p3).y);
        // cneg_fp(p3->ZZZ, p3->ZZZ, subtract);
        blst::blst_fp_cneg(&mut (*p3).zzz, &(*p3).zzz, subtract != 0);
    } else {
        // vec_zero(p3->ZZZ, 2 * sizeof(p3->ZZZ));
        vec_zero(
            &mut (*p3).zzz as *mut blst_fp as *mut u64,
            2 * size_of::<blst_fp>(),
        );
    }
}

unsafe fn p1_dadd(p3: *mut P1XYZZ, p1: *const P1XYZZ, p2: *const P1XYZZ) {
    // POINTonE1xyzz *p3, const POINTonE1xyzz *p1, const POINTonE1xyzz *p2

    // vec384 U, S, P, R;

    // if (vec_is_zero(p2->ZZZ, 2 * sizeof(p2->ZZZ)))
    if vec_is_zero(
        &(*p2).zzz as *const blst_fp as *const u8,
        2 * size_of::<blst_fp>(),
    ) != 0
    {
        // vec_copy(p3, p1, sizeof(*p3));
        vec_copy(p3 as *mut u8, p1 as *const u8, size_of::<P1XYZZ>());
        // return;
        return;
    // else if (vec_is_zero(p1->ZZZ, 2 * sizeof(p1->ZZZ)))
    } else if vec_is_zero(
        &(*p1).zzz as *const blst_fp as *const u8,
        2 * size_of::<blst_fp>(),
    ) != 0
    {
        // vec_copy(p3, p2, sizeof(*p3));
        vec_copy(p3 as *mut u8, p2 as *mut u8, size_of::<P1XYZZ>());
        // return;
        return;
    }

    let mut u = blst_fp::default();
    let mut s = blst_fp::default();
    let mut p = blst_fp::default();
    let mut r = blst_fp::default();

    // mul_fp(U, p1->X, p2->ZZ);
    blst::blst_fp_mul(&mut u, &(*p1).x, &(*p2).zz);
    // mul_fp(S, p1->Y, p2->ZZZ);
    blst::blst_fp_mul(&mut s, &(*p1).y, &(*p2).zzz);
    // mul_fp(P, p2->X, p1->ZZ);
    blst::blst_fp_mul(&mut p, &(*p2).x, &(*p1).zz);
    // mul_fp(R, p2->Y, p1->ZZZ);
    blst::blst_fp_mul(&mut r, &(*p2).y, &(*p1).zzz);
    // sub_fp(P, P, U);
    blst::blst_fp_sub(&mut p, &p, &u);
    // sub_fp(R, R, S);
    blst::blst_fp_sub(&mut r, &r, &s);

    // if (!vec_is_zero(P, sizeof(P)))
    if vec_is_zero(&p as *const blst_fp as *const u8, size_of::<blst_fp>()) == 0 {
        // vec384 PP, PPP, Q;
        let mut pp = blst_fp::default();
        let mut ppp = blst_fp::default();
        let mut q = blst_fp::default();
        // sqr_fp(PP, P);
        blst::blst_fp_sqr(&mut pp, &p);
        // mul_fp(PPP, PP, P);
        blst::blst_fp_mul(&mut ppp, &pp, &p);
        // mul_fp(Q, U, PP);
        blst::blst_fp_mul(&mut q, &u, &pp);
        // sqr_fp(p3->X, R);
        blst::blst_fp_sqr(&mut (*p3).x, &r);
        // add_fp(P, Q, Q);
        blst::blst_fp_add(&mut p, &q, &q);
        // sub_fp(p3->X, p3->X, PPP);
        blst::blst_fp_sub(&mut (*p3).x, &(*p3).x, &ppp);
        // sub_fp(p3->X, p3->X, P);
        blst::blst_fp_sub(&mut (*p3).x, &(*p3).x, &p);
        // sub_fp(Q, Q, p3->X);
        blst::blst_fp_sub(&mut q, &q, &(*p3).x);
        // mul_fp(Q, Q, R);
        blst::blst_fp_mul(&mut q, &q, &r);
        // mul_fp(p3->Y, S, PPP);
        blst::blst_fp_mul(&mut (*p3).y, &s, &ppp);
        // sub_fp(p3->Y, Q, p3->Y);
        blst::blst_fp_sub(&mut (*p3).y, &q, &(*p3).y);
        // mul_fp(p3->ZZ, p1->ZZ, p2->ZZ);
        blst::blst_fp_mul(&mut (*p3).zz, &(*p1).zz, &(*p2).zz);
        // mul_fp(p3->ZZZ, p1->ZZZ, p2->ZZZ);
        blst::blst_fp_mul(&mut (*p3).zzz, &(*p1).zzz, &(*p2).zzz);
        // mul_fp(p3->ZZ, p3->ZZ, PP);
        blst::blst_fp_mul(&mut (*p3).zz, &(*p3).zz, &pp);
        // mul_fp(p3->ZZZ, p3->ZZZ, PPP);
        blst::blst_fp_mul(&mut (*p3).zzz, &(*p3).zzz, &ppp);
    // else if (vec_is_zero(R, sizeof(R)))
    } else if vec_is_zero(&r as *const blst_fp as *const u8, size_of::<blst_fp>()) != 0 {
        // vec384 V, W, M;
        let mut v = blst_fp::default();
        let mut w = blst_fp::default();
        let mut m = blst_fp::default();

        // add_fp(U, p1->Y, p1->Y);
        blst::blst_fp_add(&mut u, &(*p1).y, &(*p1).y);
        // sqr_fp(V, U);
        blst::blst_fp_sqr(&mut v, &u);
        // mul_fp(W, V, U);
        blst::blst_fp_mul(&mut w, &v, &u);
        // mul_fp(S, p1->X, V);
        blst::blst_fp_mul(&mut s, &(*p1).x, &v);
        // sqr_fp(M, p1->X);
        blst::blst_fp_sqr(&mut m, &(*p1).x);
        // mul_by_3_fp(M, M);
        blst::blst_fp_mul_by_3(&mut m, &m);
        // sqr_fp(p3->X, M);
        blst::blst_fp_sqr(&mut (*p3).x, &m);
        // add_fp(U, S, S);
        blst::blst_fp_add(&mut u, &s, &s);
        // sub_fp(p3->X, p3->X, U);
        blst::blst_fp_sub(&mut (*p3).x, &(*p3).x, &u);
        // mul_fp(p3->Y, W, p1->Y);
        blst::blst_fp_mul(&mut (*p3).y, &w, &(*p1).y);
        // sub_fp(S, S, p3->X);
        blst::blst_fp_sub(&mut s, &s, &(*p3).x);
        // mul_fp(S, S, M);
        blst::blst_fp_mul(&mut s, &s, &m);
        // sub_fp(p3->Y, S, p3->Y);
        blst::blst_fp_sub(&mut (*p3).y, &s, &(*p3).y);
        // mul_fp(p3->ZZ, p1->ZZ, V);
        blst::blst_fp_mul(&mut (*p3).zz, &(*p1).zz, &v);
        // mul_fp(p3->ZZZ, p1->ZZZ, W);
        blst::blst_fp_mul(&mut (*p3).zzz, &(*p1).zzz, &w);
    } else {
        // vec_zero(p3->ZZZ, 2 * sizeof(p3->ZZZ));
        vec_zero(
            &mut (*p3).zzz as *mut blst_fp as *mut limb_t,
            2 * size_of::<blst_fp>(),
        );
    }
}

#[repr(C)]
#[derive(Default, Clone, Copy, Debug)]
struct P1XYZZ {
    x: blst_fp,
    y: blst_fp,
    zzz: blst_fp,
    zz: blst_fp,
}

unsafe fn p1s_bucket(
    buckets: *mut P1XYZZ,
    mut booth_idx: limb_t,
    wbits: usize,
    p: *const blst_p1_affine,
) {
    let booth_sign = (booth_idx >> wbits) & 1;
    booth_idx &= (1 << wbits) - 1;
    if booth_idx != 0 {
        booth_idx -= 1;
        p1_dadd_affine(
            buckets.wrapping_add(booth_idx.try_into().unwrap()),
            buckets.wrapping_add(booth_idx.try_into().unwrap()),
            p,
            booth_sign,
        );
    }
}

unsafe fn p1_to_jacobian(out: *mut blst_p1, input: *const P1XYZZ) {
    // POINTonE1 *out, const POINTonE1xyzz *in

    // blst::blst_p1_from_jacobian(out, in_)

    // mul_fp(out->X, in->X, in->ZZ);
    blst::blst_fp_mul(&mut (*out).x, &(*input).x, &(*input).zz);
    // mul_fp(out->Y, in->Y, in->ZZZ);
    blst::blst_fp_mul(&mut (*out).y, &(*input).y, &(*input).zzz);
    // vec_copy(out->Z, in->ZZ, sizeof(out->Z));
    vec_copy(
        &mut (*out).z as *mut blst_fp as *mut u8,
        &(*input).zz as *const blst_fp as *const u8,
        size_of::<blst_fp>(),
    );
}

unsafe fn p1_integrate_buckets(out: *mut blst_p1, buckets: *mut P1XYZZ, wbits: usize) {
    // POINTonE1xyzz ret[1], acc[1];
    let mut ret = [P1XYZZ::default()];
    let mut acc = [P1XYZZ::default()];

    // size_t n = (size_t)1 << wbits;
    let mut n = (1usize << wbits) - 1;
    // vec_copy(acc, &buckets[--n], sizeof(acc));
    vec_copy(
        &mut acc as *mut P1XYZZ as *mut u8,
        buckets.wrapping_add(n) as *const u8,
        size_of::<P1XYZZ>(),
    );
    // vec_copy(ret, &buckets[n], sizeof(ret));
    vec_copy(
        &mut ret as *mut P1XYZZ as *mut u8,
        buckets.wrapping_add(n) as *const u8,
        size_of::<P1XYZZ>(),
    );
    // vec_zero(&buckets[n], sizeof(buckets[n]));
    vec_zero(buckets.wrapping_add(n) as *mut limb_t, size_of::<P1XYZZ>());

    // while (n--)
    loop {
        if n == 0 {
            break;
        }
        n -= 1;

        // POINTonE1xyzz_dadd(acc, acc, &buckets[n]);
        p1_dadd(acc.as_mut_ptr(), acc.as_ptr(), buckets.wrapping_add(n));
        // POINTonE1xyzz_dadd(ret, ret, acc);
        p1_dadd(ret.as_mut_ptr(), ret.as_ptr(), acc.as_ptr());
        // vec_zero(&buckets[n], sizeof(buckets[n]));
        vec_zero(buckets.wrapping_add(n) as *mut limb_t, size_of::<P1XYZZ>());
    }

    // POINTonE1xyzz_to_Jacobian(out, ret);
    // blst::blst_p1_from_jacobian(out, ret.as_ptr() as *const blst_p1);
    p1_to_jacobian(out, ret.as_ptr());
}

// unsafe fn p1_prefetch() {
// booth_idx &= (1 << wbits) - 1;
// if (booth_idx--)
//     vec_prefetch(&buckets[booth_idx], sizeof(buckets[booth_idx]));
// }

#[allow(clippy::too_many_arguments)]
unsafe fn p1s_tile_pippenger(
    ret: *mut blst_p1,
    mut points: *const *const blst_p1_affine,
    mut npoints: usize,
    mut scalars: *const *const byte,
    nbits: usize,
    buckets: *mut limb_t,
    mut bit0: usize,
    wbits: usize,
    cbits: usize,
) {
    // limb_t wmask, wval, wnxt;
    // size_t i, z, nbytes;
    // const byte *scalar = *scalars++;
    let scalar = *scalars;
    scalars = scalars.wrapping_add(1);
    // const POINTonE1_affine *point = *points++;
    let mut point = *points;
    points = points.wrapping_add(1);
    // nbytes = (nbits + 7) / 8;
    let nbytes = (nbits + 7) / 8;
    // wmask = ((limb_t)1 << (wbits + 1)) - 1;
    let wmask = ((1 as limb_t) << (wbits + 1)) - 1;
    // z = is_zero(bit0);
    let z = is_zero((bit0).try_into().unwrap());
    // bit0 -= z ^ 1;
    bit0 -= (z ^ 1) as usize;
    // wbits += z ^ 1;
    let wbits = wbits + (z ^ 1) as usize;
    // wval = (get_wval_limb(scalar, bit0, wbits) << z) & wmask;
    let wval = (get_wval_limb(scalar, bit0, wbits) << z) & wmask;
    // wval = booth_encode(wval, cbits);
    let mut wval = booth_encode(wval, cbits);
    // scalar = *scalars ? *scalars++ : scalar + nbytes;
    let mut scalar = if (*scalars).is_null() {
        scalar.wrapping_add(nbytes)
    } else {
        let v = *scalars;
        scalars = scalars.wrapping_add(1);
        v
    };
    // wnxt = (get_wval_limb(scalar, bit0, wbits) << z) & wmask;
    let wnxt = (get_wval_limb(scalar, bit0, wbits) << z) & wmask;
    // wnxt = booth_encode(wnxt, cbits);
    let mut wnxt = booth_encode(wnxt, cbits);
    // npoints--;
    npoints -= 1;

    // POINTonE1_bucket(buckets, wval, cbits, point);
    p1s_bucket(buckets as *mut P1XYZZ, wval, cbits, point);
    // for (i = 1; i < npoints; i++)
    for _i in 1..npoints {
        // wval = wnxt;
        wval = wnxt;
        // scalar = *scalars ? *scalars++ : scalar + nbytes;
        scalar = if (*scalars).is_null() {
            scalar.wrapping_add(nbytes)
        } else {
            let v = *scalars;
            scalars = scalars.wrapping_add(1);
            v
        };
        // wnxt = (get_wval_limb(scalar, bit0, wbits) << z) & wmask;
        wnxt = (get_wval_limb(scalar, bit0, wbits) << z) & wmask;
        // wnxt = booth_encode(wnxt, cbits);
        wnxt = booth_encode(wnxt, cbits);
        // POINTonE1_prefetch(buckets, wnxt, cbits);
        // p1_prefetch(buckets, wnxt, cbits);
        // TODO:

        // point = *points ? *points++ : point + 1;
        point = if (*points).is_null() {
            point.wrapping_add(1)
        } else {
            let v = *points;
            points = points.wrapping_add(1);
            v
        };
        // POINTonE1_bucket(buckets, wval, cbits, point);
        p1s_bucket(buckets as *mut P1XYZZ, wval, cbits, point);
    }
    // point = *points ? *points++ : point + 1;
    point = if (*points).is_null() {
        point.wrapping_add(1)
    } else {
        *points
    };
    // POINTonE1_bucket(buckets, wnxt, cbits, point);
    p1s_bucket(buckets as *mut P1XYZZ, wnxt, cbits, point);
    // POINTonE1_integrate_buckets(ret, buckets, cbits - 1);
    p1_integrate_buckets(ret, buckets as *mut P1XYZZ, cbits - 1);
}

unsafe fn pippenger(
    ret: *mut blst_p1,
    points: *const *const blst_p1_affine,
    npoints: usize,
    scalars: *const *const byte,
    nbits: usize,
    buckets: *mut limb_t,
    window: usize,
) {
    // size_t i, wbits, cbits, bit0 = nbits;
    // POINTonE1 tile[1];
    let window = if window != 0 {
        window
    } else {
        pippenger_window_size(npoints)
    };

    vec_zero(buckets, size_of::<limb_t>() << (window - 1));
    vec_zero(ret as *mut limb_t, size_of::<blst_p1>());

    let mut wbits: usize = nbits % window;
    let mut cbits: usize = wbits + 1;
    let mut bit0: usize = nbits;
    let mut tile = [blst_p1::default(); 1];

    loop {
        bit0 -= wbits;
        if bit0 == 0 {
            break;
        }

        p1s_tile_pippenger(
            tile.as_mut_ptr(),
            points,
            npoints,
            scalars,
            nbits,
            buckets,
            bit0,
            wbits,
            cbits,
        );
        blst_p1_add(ret, ret, tile.as_mut_ptr());
        for _ in 0..window {
            blst_p1_double(ret, ret);
        }
        cbits = window;
        wbits = window;
    }
    p1s_tile_pippenger(
        tile.as_mut_ptr(),
        points,
        npoints,
        scalars,
        nbits,
        buckets,
        0,
        wbits,
        cbits,
    );
    blst_p1_add(ret, ret, tile.as_mut_ptr());

    // // vec_zero(buckets, sizeof(buckets[0]) << (window - 1));
    // // vec_zero(ret, sizeof(*ret));
    // // wbits = nbits % window;
    // // cbits = wbits + 1;
    // // while (bit0 -= wbits)
    // // {
    // //     POINTonE1s_tile_pippenger(tile, points, npoints, scalars, nbits, buckets, bit0, wbits, cbits);
    // //     POINTonE1_dadd(ret, ret, tile, NULL);
    // //     for (i = 0; i < window; i++)
    // //         POINTonE1_double(ret, ret);
    // //     cbits = wbits = window;
    // // }
    // // POINTonE1s_tile_pippenger(tile, points, npoints, scalars, nbits, buckets, 0, wbits, cbits);
    // // POINTonE1_dadd(ret, ret, tile, NULL);
}

pub unsafe fn msm(
    ret: *mut blst_p1,
    points: *const *const blst_p1_affine,
    npoints: usize,
    scalars: *const *const byte,
    nbits: usize,
    scratch: *mut limb_t,
) {
    if npoints == 1 {
        blst_p1_from_affine(ret, *points);
        blst_p1_mult(ret, ret, *scalars, nbits);
        return;
    }

    if npoints * size_of::<blst_p1_affine>() * 8 * 3 <= (144 * 1024) {
        let mut table = vec![blst_p1_affine::default(); npoints * 8];
        blst_p1s_mult_wbits_precompute(table.as_mut_ptr(), 4, points, npoints);
        blst_p1s_mult_wbits(ret, table.as_ptr(), 4, npoints, scalars, nbits, null_mut());
        return;
    }

    // if ((npoints * sizeof(POINTonE1_affine) * 8 * 3) <= SCRATCH_LIMIT)
    // {
    //     POINTonE1_affine *table = alloca(npoints * sizeof(POINTonE1_affine) * 8);
    //     POINTonE1s_precompute_wbits(table, 4, points, npoints);
    //     POINTonE1s_mult_wbits(ret, table, 4, npoints, scalars, nbits, NULL);
    //     return;
    // }
    // POINTonE1s_mult_pippenger(ret, points, npoints, scalars, nbits, scratch, 0);

    pippenger(ret, points, npoints, scalars, nbits, scratch, 0);
}

#[cfg(test)]
mod tests {
    use crate::msm::booth_encode;

    #[test]
    fn booth_encode_must_produce_correct_results() {
        assert_eq!(booth_encode(0, 1), 0);
        assert_eq!(booth_encode(0, 5), 0);
        assert_eq!(booth_encode(1, 1), 1);
        assert_eq!(booth_encode(55, 5), 18446744073709551588);
    }
}
