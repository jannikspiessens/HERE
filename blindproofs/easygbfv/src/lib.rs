#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![feature(test)]
#![feature(allocator_api)]

use feanor_math::ring::*;

use crate::gbfv::GBFV;


pub mod gbfv;

pub mod hommatmul;

pub mod params;


pub const LOG: bool = true;


pub mod tests {
    use super::*;
    use rand::RngCore;
    use rand_seeder::{Seeder, SipRng};
    use feanor_math::rings::finite::{FiniteRingStore, FiniteRing};
    use crate::params::get_gbfv_128bit;

    pub fn gen_random<R>(ring: &R, len: usize, seed: Option<&str>) -> Vec<El<R>>
        where R: FiniteRingStore<Type: FiniteRing>
    {
        let mut rng: SipRng = Seeder::from(seed).into_rng();
        (0..len).map(|_| ring.random_element(|| rng.next_u64())).collect::<Vec<_>>()
    }

    pub fn test_rot<R: RingStore>(ring: &R, inp: &Vec<El<R>>, out: &Vec<El<R>>, by: usize) {
        assert!(inp.len() == out.len());
        assert!((0..inp.len()).all(|i| ring.eq_el(&inp[i], &out[(i+by)%out.len()])))
    }

    pub fn get_gbfv_test(i: usize, log2_N: usize, qbits: usize, pack_factor: Option<usize>) -> GBFV<LOG>
    {
        get_gbfv_128bit(i, log2_N, qbits, pack_factor)
        // get_gbfv_64bit(i, log2_N, qbits, pack_factor)
        // get_gbfv_32bit(i, log2_N, qbits, pack_factor)
        // get_gbfv_16bit(i, log2_N, qbits, pack_factor)
    }
}

