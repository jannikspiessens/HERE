use feanor_math::homomorphism::{CanIso, CanIsoFromTo};
use feanor_math::ring::RingStore;
use easygbfv::{
    gbfv::{
        SlotRing,
        Ciphertext as Ct,
        GBFV,
        PublicKey
    },
};
use proofs::{
    util::matmul::MatrixMul,
    codes::LinearCode
};


pub mod foldablecodes;


pub struct BlindCode<'a, C, Rg, const LOG: bool>
    where C: LinearCode<R = Rg>, Rg: RingStore,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<Rg as RingStore>::Type>
{
    gbfv: &'a GBFV<LOG>,
    code: &'a C,
    iso: CanIso<Rg, SlotRing>
} 

impl<'a, C, Rg, const LOG: bool> BlindCode<'a, C, Rg, LOG>
    where C: LinearCode<R = Rg>, Rg: RingStore + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<Rg as RingStore>::Type>
{
    pub fn new(gbfv: &'a GBFV<LOG>, code: &'a C) -> Self {
        // TODO: allow code.generator().columns() to divide gbfv.pack()
        assert!(code.generator().columns() % gbfv.pack() == 0);
        assert!(code.generator().rows() % gbfv.pack() == 0);
        let iso = gbfv.slot_ring().clone().into_can_iso(code.ring().clone()).ok().unwrap();
        Self {
            gbfv,
            code,
            iso
        }
    }

    pub fn code(&self) -> &C {
        self.code
    }

    pub fn ring(&self) -> &Rg {
        self.code().ring()
    }

    pub fn iso(&self) -> &CanIso<Rg, SlotRing> {
        &self.iso
    }

    // TODO: exploit fact that self.code is RS code? -> deal with bitreversals
    pub fn encode(&self, input: &[Ct], pk: &PublicKey) -> Vec<Ct> {
        self.gbfv.hom_matmul(self.code.generator(), input, pk)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::ring::El;
    use feanor_math::rings::finite::FiniteRingStore;
    use proofs::util::gen_vector;
    use proofs::codes::RScode;
    use easygbfv::{gbfv::SlotField, tests::get_gbfv_test};
    use crate::util::tests::test_correctness;
    use crate::codes::BlindCode;

    #[test]
    fn test_blindcode() {

        let gbfv = get_gbfv_test(0, 8, 200, None);
        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);
        let slotfield = gbfv.slot_field();

        let k0 = gbfv.pack();
        let c = 2;

        let rscode = RScode::new(&slotfield, k0, k0*c);
        
        let bcode = &BlindCode::new(&gbfv, &rscode);
        let toslot = bcode.iso().inv();

        let input = gen_vector::<El<SlotField>>(||
            slotfield.random_element(rand::random::<u64>), k0);
        let ctin = gbfv.enc_slots_map_ref(input.iter(), &toslot, &sk);

        let ctcode = bcode.encode(&ctin, &pk);

        test_correctness(&gbfv, &slotfield, &sk, ctcode, bcode.code.encode(&input), &toslot);
    }
}
