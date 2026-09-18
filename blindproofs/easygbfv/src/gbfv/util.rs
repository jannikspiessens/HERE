use itertools::Itertools;

use feanor_math::ring::*;
use feanor_math::seq::{VectorView, VectorFn};
use feanor_math::group::AbelianGroupStore;

use fheanor::number_ring::{
    NumberRingQuotientStore,
    galois::GaloisGroupEl
};
use fheanor::clpx::{ Pow2CLPX, CLPXInstantiation };
use fheanor::circuit::{ Coefficient, evaluator::CircuitEvaluator };

use proofs::util::ZZbig;

use crate::{
    GBFV,
    gbfv::{
        PublicKey, Ciphertext,
        CiphertextRing, CiphertextRingBase,
        PTCircuit
    }
};


pub struct GBFVEvaluator<'a, const LOG: bool> {
    gbfv: &'a GBFV<LOG>,
    pk: &'a PublicKey
}

impl<'a, const LOG: bool> GBFVEvaluator<'a, LOG> {
    pub fn new(gbfv: &'a GBFV<LOG>, pk: &'a PublicKey) -> Self {
        Self { gbfv, pk }
    }
}

impl<'a, 'b, const LOG: bool> CircuitEvaluator<'b, Ciphertext, CiphertextRingBase>
    for GBFVEvaluator<'a, LOG>
{
    fn supports_gal(&self) -> bool { true }

    fn supports_mul(&self) -> bool { true }

    fn add_constant(&mut self, val: Ciphertext, constant: &'b Coefficient<CiphertextRingBase>)
        -> Ciphertext
    {
        let adder = |inp: El<CiphertextRing>| {
            constant.add_to(inp, self.gbfv.ciphertext_ring())
        };
        (adder(val.0), adder(val.1))
    }

    fn gal(&mut self, val: Ciphertext, gs: &'b [GaloisGroupEl]) -> Vec<Ciphertext> {
        let gks = gs.as_fn().map_fn(|g| &self.pk.gks.iter().filter(|(gk_g, _)|
            self.gbfv.hciso.galois_group().eq_el(g, gk_g))
                .next().expect("galois key not present").1);
        if gs.len() == 1 {
            vec![<Pow2CLPX as CLPXInstantiation>::hom_galois(self.gbfv.plaintext_ring(),
                self.gbfv.ciphertext_ring(), val, &gs[0], gks.at(0))]
        } else {
            <Pow2CLPX as CLPXInstantiation>::hom_galois_many(self.gbfv.plaintext_ring(),
                self.gbfv.ciphertext_ring(), val, gs, &gks)
        }
    }

    fn inner_prod<'c, I>(&mut self, mut data: I) -> Ciphertext
        where I: Iterator<Item = (&'b Coefficient<CiphertextRingBase>, &'c Ciphertext)>,
            CiphertextRingBase: 'b,
            Ciphertext: 'c
    {
        if let Some((coeff, ciphertext)) = data.next() {
            let mut result = if let Coefficient::One = coeff {
                self.gbfv.clone_ct(ciphertext)
            } else if let Coefficient::NegOne = coeff {
                self.gbfv.negate(self.gbfv.clone_ct(ciphertext))
            } else if let Coefficient::Other(coeff) = coeff {
                self.gbfv.hom_mul_plain_single_small_ref(ciphertext, coeff)
            } else {
                unreachable!()
            };
            for (coeff, ciphertext) in data {
                if let Coefficient::One = coeff {
                    result = self.gbfv.hom_add_single(result, self.gbfv.clone_ct(ciphertext));
                } else if let Coefficient::NegOne = coeff {
                    result = self.gbfv.hom_sub_single(result, self.gbfv.clone_ct(ciphertext));
                } else if let Coefficient::Other(coeff) = coeff {
                    result = self.gbfv.hom_mul_plain_add_single_small_ref(result, ciphertext, coeff)
                } else {
                    unreachable!()
                }
            }
            return result;
        } else {
            return self.gbfv.ct_zero()
        }
    }

    fn mul(&mut self, lhs: Ciphertext, rhs: Ciphertext) -> Ciphertext {
        self.gbfv.hom_mul(lhs, rhs, &self.pk)
    }

    fn square(&mut self, val: Ciphertext) -> Ciphertext {
        self.gbfv.hom_square_single(val, self.pk)
    }
}


impl<const LOG: bool> std::fmt::Display for GBFV<LOG> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let (m, p, pack, npf) = self.id();
        write!(f, "p = {}\nlog2(m) = {}\nt(X) = {}\nnative pack = {}\npack = {}",
            ZZbig.format(&p), m.ilog2(), 
            self.plaintext_ring().get_ring().ZZX().format(self.plaintext_ring().get_ring().t()),
            pack*npf, pack)
    }
}

fn sumslots_circuit_shallow<const LOG: bool>(gbfv: &GBFV<LOG>) -> PTCircuit
{
    let ring = gbfv.hciso().ring();
    let p = gbfv.pack();
    let coeffs = (0..p).map(|_| Coefficient::One).collect_vec();

    PTCircuit::linear_transform(&coeffs, ring).compose(
        PTCircuit::identity(1, ring).output_times(p, ring), ring)
}

fn sumslots_circuit_deep<const LOG: bool>(gbfv: &GBFV<LOG>) -> PTCircuit
{
    assert!(gbfv.pack().is_power_of_two());
    let ring = gbfv.hciso().ring();
    let lp = gbfv.pack().ilog2();
    let gg = gbfv.ciphertext_ring().acting_galois_group();
    let coeffs = (0..2).map(|_| Coefficient::One).collect_vec();

    let mut tmp = PTCircuit::identity(1, ring);
    (0..lp).for_each(|i|
        tmp = PTCircuit::linear_transform(&coeffs, ring).compose(
            PTCircuit::identity(1, ring).tensor(
                PTCircuit::gal(gbfv.get_rot_galois_el(1 << i), gg, ring), ring)
            .compose(tmp.clone(ring).output_twice(ring), ring), ring)
    );
    tmp
}

pub fn compress_circuit<const DEEP: bool, const LOG: bool>(gbfv: &GBFV<LOG>, len: usize)
    -> PTCircuit
{
    assert!(len <= gbfv.pack());
    let ring = gbfv.hciso().ring();
    let sr = gbfv.slot_ring();
    let sum_circuit = |gbfv: &GBFV<LOG>| {
        if DEEP { sumslots_circuit_deep(gbfv) } else { sumslots_circuit_shallow(gbfv) }
    };
    let mut tmp = sum_circuit(gbfv);
    for _ in 1..len { tmp = tmp.tensor(sum_circuit(gbfv), ring) };

    let coeffs = (0..len).map(|i|
        Coefficient::Other(gbfv.encode_slots_single((0..gbfv.pack()).map(|j|
            if j == i { sr.one() } else { sr.zero() })))).collect_vec();

    PTCircuit::linear_transform(&coeffs, ring).compose(tmp, ring)
}

