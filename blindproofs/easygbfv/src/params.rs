use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::rings::poly::dense_poly::DensePolyRing;
use feanor_math::rings::poly::PolyRingStore;
use feanor_math::homomorphism::Homomorphism;

use proofs::util::ZZbig;
use crate::{LOG, gbfv::{GBFV, GBFV_PtParams}};


pub fn get_gbfv_16bit(i: usize, log2_N: usize, qbits: usize, pack_factor: Option<usize>)
    -> GBFV<LOG>
{
    let m = 1 << (log2_N + 1);
    let k = m >> (5 - i);
    let b = ZZbig.negate(ZZbig.pow(ZZbig.int_hom().map(2), 1 << i));
    let ZZX = DensePolyRing::new(ZZbig, "X");
    let t = ZZX.from_terms([(b, 0), (ZZbig.one(), k)]);
    let params = GBFV_PtParams {
        log2_N,
        k,
        p: ZZbig.get_ring().parse("65537", 10).unwrap(),
        t,
        pack_factor: pack_factor.unwrap_or(1),
        log2_q: qbits+5..qbits+10,
        log2_t_can_bound: 2
    };

    let gbfv = GBFV::<LOG>::new(params, None);
    println!("{gbfv}");

    return gbfv;
}

pub fn get_gbfv_32bit(i: usize, log2_N: usize, qbits: usize, pack_factor: Option<usize>)
    -> GBFV<LOG>
{
    let m = 1 << (log2_N + 1);
    let k = m >> (3 - i);
    let b = ZZbig.negate(ZZbig.pow(ZZbig.int_hom().map(288), 1 << i));
    let ZZX = DensePolyRing::new(ZZbig, "X");
    let t = ZZX.from_terms([(b, 0), (ZZbig.one(), k)]);
    let params = GBFV_PtParams {
        log2_N,
        k,
        p: ZZbig.get_ring().parse("6879707137", 10).unwrap(),
        t,
        pack_factor: pack_factor.unwrap_or(1),
        log2_q: qbits+5..qbits+10,
        log2_t_can_bound: 9
    };

    let gbfv = GBFV::<LOG>::new(params, None);
    println!("{gbfv}");

    return gbfv;
}

pub fn get_gbfv_64bit(i: usize, log2_N: usize, qbits: usize, pack_factor: Option<usize>)
    -> GBFV<LOG>
{
    assert!(i == 0);
    let m = 1 << (log2_N + 1);
    let k = m >> 6;
    let ZZX = DensePolyRing::new(ZZbig, "X");
    let [t] = ZZX.with_wrapped_indeterminate(|X|
        [X.pow_ref(22*8) - X.pow_ref(11*8) - X.pow_ref(11*8) + 4]);
    let params = GBFV_PtParams {
        log2_N,
        k,
        p: ZZbig.get_ring().parse("18446744069414584321", 10).unwrap(),
        t,
        pack_factor: pack_factor.unwrap_or(1),
        log2_q: qbits+5..qbits+10,
        log2_t_can_bound: 3
    };

    let gbfv = GBFV::<LOG>::new(params, None);
    println!("{gbfv}");

    return gbfv;
}


pub fn get_gbfv_128bit(i: usize, log2_N: usize, qbits: usize, pack_factor: Option<usize>)
    -> GBFV<LOG>
{
    let m = 1 << (log2_N + 1);
    let k = m >> (5 - i);
    let b = ZZbig.negate(ZZbig.pow(ZZbig.int_hom().map(248), 1 << i));
    let ZZX = DensePolyRing::new(ZZbig, "X");
    let t = ZZX.from_terms([(b, 0), (ZZbig.one(), k)]);
    let params = GBFV_PtParams {
        log2_N,
        k,
        p: ZZbig.get_ring().parse("204751406252581656212043048442748993537", 10).unwrap(),
        t,
        pack_factor: pack_factor.unwrap_or(1),
        log2_q: qbits+5..qbits+10,
        log2_t_can_bound: 9
    };

    let gbfv = GBFV::<LOG>::new(params, None);
    println!("{gbfv}");

    return gbfv;
}
