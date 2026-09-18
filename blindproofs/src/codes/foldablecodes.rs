use feanor_math::homomorphism::{CanIso, CanIsoFromTo};
use feanor_math::ring::{El, RingStore};
use easygbfv::gbfv::{
    SlotRing,
    Ciphertext as Ct,
    GBFV,
    PublicKey
};
use proofs::{
    codes::{
        LinearCode,
        foldablecodes::FoldableCode
    },
    util::{gen_vector, bits_from_int, int_from_bits}
};
use crate::codes::BlindCode;

pub struct BlindFoldableCode<'a, FC, Rg, const LOG: bool>
    where FC: FoldableCode<R = Rg, C: LinearCode<R = Rg>>, Rg: RingStore + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<Rg as RingStore>::Type>
{
    gbfv: &'a GBFV<LOG>,
    foldablecode: &'a FC,
    bcode: BlindCode<'a, FC::C, Rg, LOG>
}

impl<'a, FC, Rg, const LOG: bool> BlindFoldableCode<'a, FC, Rg, LOG>
    where FC: FoldableCode<R = Rg, C: LinearCode<R = Rg> + Clone>, Rg: RingStore + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<Rg as RingStore>::Type>
{
    pub fn new(gbfv: &'a GBFV<LOG>, foldablecode: &'a FC) -> Self {
        let bcode = BlindCode::new(gbfv, foldablecode.G0code());
        Self {
            gbfv,
            foldablecode,
            bcode
        }
    }

    pub fn ring(&self) -> &Rg {
        self.bcode.ring()
    }

    pub fn iso(&self) -> &CanIso<Rg, SlotRing> {
        self.bcode.iso()
    }

    pub fn foldablecode(&self) -> &FC {
        self.foldablecode
    }

    pub fn bcode(&self) -> &BlindCode<'a, FC::C, Rg, LOG> {
        &self.bcode
    }

    pub fn encode(&self, input: &[Ct], pk: &PublicKey) -> Vec<Ct> {
        let browlen = self.foldablecode.n(0) / self.gbfv.pack();
        // TODO: allow code.generator().columns() to divide gbfv.pack()
        let bcollen = self.foldablecode.k(0) / self.gbfv.pack();
        assert!(input.len() % bcollen == 0);

        // TODO: allow code.generator().columns() to divide gbfv.pack()
        let d = self.foldablecode.d();
        assert!(input.len() / bcollen == 1 << d);

        let output_len = self.foldablecode.c()*input.len();
        let mut res = gen_vector::<Ct>(|| self.gbfv.ct_zero(), output_len);

        res.chunks_exact_mut(browlen).zip(input.chunks_exact(bcollen)).for_each(|(out, inp)| {
            out.iter_mut().zip(self.bcode.encode(inp, pk)).for_each(|(oct, ict)| *oct = ict)
        });

        if d > 0 {
            self.encode_deep(&mut res, d, browlen);
            // self.encode_shallow(&mut res, d, browlen, 0);

            // depth 2 encoding
            // self.encode_shallow(&mut res[..output_len/2], d - 1, browlen, 0);
            // self.encode_shallow(&mut res[output_len/2..], d - 1, browlen, 0);
            // self.encode_shallow(&mut res, 1, browlen*(1 << (d - 1)), d - 1);
            // TODO: make general for depth d' < d
        }
        res
    }

    #[allow(dead_code)] 
    fn encode_shallow(&self, res: &mut [Ct], depth: usize, baselen: usize, starting_depth: usize) {
        let input = self.gbfv.clone_cts(res.iter());
        // let mut ws = gen_vector::<El<Rg>>(||
        //     self.foldablecode.ring().one(), baselen*self.gbfv.pack());
        let baselenslots = baselen*self.gbfv.pack();
        let toslot = self.iso().inv();
        
        res.chunks_exact_mut(baselen).enumerate().for_each(|(i, resbrows)| {
            let ibits = bits_from_int(i, depth).collect::<Vec<_>>();
            input.chunks_exact(baselen).enumerate().for_each(|(j, inpbrows)| {
                if j == 0 {
                    resbrows.iter_mut().zip(self.gbfv.clone_cts(inpbrows.iter())).for_each(
                        |(resct, inpct)| *resct = inpct);
                } else {
                    // if !(i == 0 && j == 0) {
                    //     ws.iter_mut().for_each(|wsk| *wsk = self.foldablecode.ring().one());
                    // }
                    let mut ws = gen_vector::<El<Rg>>(||
                        self.foldablecode.ring().one(), baselen*self.gbfv.pack());
                    let mut signpos = true;
                    bits_from_int(j, depth).enumerate().for_each(|(bjind, bj)| {
                        if bj == 1 {
                            let tmp = int_from_bits(ibits[..bjind].iter().cloned());
                            let tji = self.foldablecode.t(starting_depth + bjind)
                                .skip(tmp*baselenslots).take(baselenslots);
                            ws.iter_mut().zip(tji).for_each(|(wsk, tjik)|
                                self.foldablecode.ring().mul_assign_ref(wsk, tjik));
                            if ibits[bjind] == 1 {
                                signpos = !signpos;
                            }
                        }
                    });
                    if !signpos {
                        ws.iter_mut().for_each(|wsk| self.foldablecode.ring().negate_inplace(wsk));
                    }
                    self.gbfv.hom_add_assign(resbrows.iter_mut(), self.gbfv.hom_mul_plain_map(
                            inpbrows, ws.into_iter(), &toslot).iter());
                    // TODO: try to use ref here?
                    // let lol = self.gbfv.hom_mul_plain_map_ref(inpbrows, ws.iter(), &self.bcode.hom);
                    // self.gbfv.hom_add_assign(resbrows.iter_mut(), lol.iter());
                }
            });
        });
    }

    #[allow(dead_code)] 
    fn encode_deep(&self, res: &mut [Ct], d: usize, browlen: usize) {
        let mut ws = gen_vector::<Ct>(|| self.gbfv.ct_zero(), res.len()/ 2);
        let toslot = self.iso().inv();

        for dind in 0..d {
            let chunksize = browlen*(1 << dind);

            // compute rt and store in the workspace
            ws.chunks_exact_mut(chunksize)
                .zip(res.chunks_exact(chunksize).skip(1).step_by(2)).for_each(|(wschunk, r)|
                    wschunk.iter_mut().zip(self.gbfv.hom_mul_plain_map_ref(r,
                        self.foldablecode.t(dind), &toslot)).for_each(|(wsi, o)| *wsi = o));

            // add rt to all left parts and subtract it from all right parts
            res.chunks_exact_mut(chunksize*2).zip(ws.chunks_exact(chunksize)).for_each(|(lr, rt)| {
                let (l, r) = lr.split_at_mut(chunksize);
                self.gbfv.hom_sub_assign_to(r.iter_mut(), l.iter(), rt.iter());
                self.gbfv.hom_add_assign(l.iter_mut(), rt.iter());
            });
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::rings::finite::FiniteRingStore;
    use proofs::util::gen_vector;
    use proofs::codes::foldablecodes::RSFoldableCode;
    use easygbfv::{gbfv::SlotField, tests::get_gbfv_test};
    use crate::util::tests::test_correctness;

    #[test]
    fn test_blindfoldablecode() {

        let gbfv = get_gbfv_test(0, 8, 200, None);
        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);
        let slotfield = gbfv.slot_field();

        let k0 = gbfv.pack();
        let c = 2;
        let d = 3; 

        let mfc = RSFoldableCode::new(&slotfield, k0, c, Some(d));
        let bfc = BlindFoldableCode::new(&gbfv, &mfc);
        let toslot = bfc.bcode().iso().inv();

        let input = gen_vector::<El<SlotField>>(||
            slotfield.random_element(rand::random::<u64>), k0*(1 << d));
        let ctin = gbfv.enc_slots_map_ref(input.iter(), &toslot, &sk);

        let bfcode = bfc.encode(&ctin, &pk);

        println!("Noise budget: {}", gbfv.noise_budget(&bfcode, &sk));

        test_correctness(&gbfv, &slotfield, &sk, bfcode,
            bfc.foldablecode.encode(&input), &toslot);
    }
}
