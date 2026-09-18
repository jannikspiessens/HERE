use itertools::Itertools;
use tracing::instrument;

use feanor_math::rings::multivariate::MultivariatePolyRingStore;
use feanor_math::homomorphism::{CanHom, CanIso, CanIsoFromTo, Homomorphism};
use feanor_math::ring::{El, RingStore, RingBase};
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::poly::PolyRingStore;
use feanor_math::field::{Field, FieldStore};
use easygbfv::{
    gbfv::{
        SlotRing,
        Ciphertext as Ct,
        GBFV,
        PublicKey, SecretKey
    }
};
use proofs::{
    commit::{
        MultilinearPCS, 
        basefold::{
            BaseFoldPCS, BSCF, BaseFoldSumcheck,
            BaseFoldProof, BaseFoldCommitment,
            // basefold_evalscalars,
        }
    },
    multilinear::{
        evalscalars_to_coeffscalars,
        // sumcheck::SCMultilinearIterator,
    },
    codes::{
        foldablecodes::FoldableCode,
        LinearCode,
    }
};
use crate::{
    multilinear::{
        univar_evaluate_at_fromctcoeff,
        multilinear_evaluate_at_fromctcoeff
    },
    codes::foldablecodes::BlindFoldableCode
};


pub struct BlindFoldCommitment{
    bcode_el: Vec<Ct>
}

impl BlindFoldCommitment {
    pub fn new(bcode_el: Vec<Ct>) -> Self {
        Self { bcode_el }
    }
}

pub struct BlindFoldProof {
    bcode_els: Vec<Vec<Ct>>,
    sumcheck_els: Vec<Vec<Ct>>,
    sumcheck_last: Vec<Ct>
}

impl BlindFoldProof {
    pub fn noise_budget<const LOG: bool>(&self, gbfv: &GBFV<LOG>, sk: &SecretKey)
        -> usize
    {
        gbfv.noise_budget_iter(
            self.bcode_els.iter().flatten().chain(
                self.sumcheck_els.iter().flatten()
            ).chain(self.sumcheck_last.iter()), sk
        )
    }
}

pub struct BlindFoldPCS<'a, FC, SC, const LOG: bool>
    where FC: FoldableCode<R = BSCF<SC>>, SC: BaseFoldSumcheck<'a>, BSCF<SC>: Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<BSCF<SC> as RingStore>::Type>
{
    gbfv: &'a GBFV<LOG>,
    bf: &'a BaseFoldPCS<'a, FC, SC>,
    bfc: BlindFoldableCode<'a, FC, BSCF<SC>, LOG>,
    denoms: Vec<Vec<El<BSCF<SC>>>>
}

impl<'a, FC, SC, const LOG: bool> BlindFoldPCS<'a, FC, SC, LOG>
    where FC: FoldableCode<R = BSCF<SC>, C: Clone>, SC: BaseFoldSumcheck<'a>, BSCF<SC>: Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<BSCF<SC> as RingStore>::Type>
{
    pub fn new(gbfv: &'a GBFV<LOG>, bfc: BlindFoldableCode<'a, FC, BSCF<SC>, LOG>,
        bf: &'a BaseFoldPCS<'a, FC, SC>) -> Self
    {
        assert!(bfc.foldablecode().k(0).is_power_of_two());
        assert!(bf.polyring().indeterminate_count() ==
            bfc.foldablecode().d() + bfc.foldablecode().k(0).ilog2() as usize);
        // do some precomputation
        let denoms = (0..bfc.foldablecode().d()).map(|i| bfc.foldablecode().t(i).map(
            |ti| bfc.ring().get_ring().mul_int_ref(ti, 2)).collect_vec()).collect_vec();
        Self {
            gbfv,
            bf,
            bfc,
            denoms
        }
    }

    pub fn varcount(&self) -> usize {
        self.bf.polyring().indeterminate_count()
    }

    pub fn field(&self) -> &BSCF<SC> {
        self.bfc.ring()
    }

    pub fn iso(&self) -> &CanIso<BSCF<SC>, SlotRing> {
        &self.bfc.iso()
    }

    pub fn get_gbfv(&self) -> &GBFV<LOG> {
        &self.gbfv
    }

    pub fn get_plain(&self) -> &BaseFoldPCS<'a, FC, SC> {
        &self.bf
    }
}

// pub fn sumcheck_sum_blindfold<'a, 'b, F, const LOG: bool>(gbfv: &'a GBFV<LOG>, field: &F,
//     hom: &CanHom<&'a F, &'a SlotRing>, coeff: &[Ct], z: &[El<F>], challenges: &[El<F>],
//     sumct: Option<Ct>, sum: Option<El<F>>) -> Vec<Ct>
//     where F: RingStore<Type: Field>,
//           <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
// {
//     let d = z.len();
//     assert!(coeff.len().is_power_of_two());
//     let logcoefflen = coeff.len().ilog2() as usize;
//     assert!(gbfv.pack().is_power_of_two());
//     let logpack = gbfv.pack().ilog2() as usize;
//     assert!(d == logpack + logcoefflen);
//     let i = challenges.len();
//     assert!(i + logpack < d);
//     let dmini = d - i;

//     let mut scalars = basefold_evalscalars(field, z, challenges, dmini).collect_vec();
//     evalscalars_to_coeffscalars(field, d - 1, &mut scalars);

//     let ctcoeffiter1 = SCMultilinearIterator::new(coeff, dmini - logpack, i, false);
//     let cttmp1 = gbfv.hom_mul_plain_add_map_ref(ctcoeffiter1, scalars.iter(), hom);

//     let zdmini = &z[dmini - 1];
//     let cttmp0 = if let Some(sumct) = sumct {
//         assert!(sum.is_none());
//         gbfv.hom_sub(&sumct, &gbfv.hom_mul_plainslot_single_map_ref(&cttmp1, zdmini, hom))
//     } else {
//         if let Some(sum) = sum {
//             gbfv.hom_add_plain_single(
//                 gbfv.hom_mul_plainslot_single_map(&cttmp1,
//                     field.negate(field.clone_el(zdmini)), hom),
//                 gbfv.enc_firstslot(hom.map_ref(&sum)))
//         } else {
//             let ctcoeffiter0 = SCMultilinearIterator::new(coeff, dmini - logpack, i, true);
//             gbfv.hom_mul_plain_add_map_ref(ctcoeffiter0, scalars.iter(), hom)
//         }
//     };

//     let oneminz = field.sub_ref_snd(field.one(), zdmini);
//     let twozminone = field.sub(field.get_ring().mul_int_ref(zdmini, 2), field.one());
//     vec![
//         gbfv.hom_mul_plainslot_single_map_ref(&cttmp0, &oneminz, hom),
//         gbfv.hom_add(
//             &gbfv.hom_mul_plainslot_single_map_ref(&cttmp0, &twozminone, hom),
//             &gbfv.hom_mul_plainslot_single_map_ref(&cttmp1, &oneminz, hom)
//         ),
//         gbfv.hom_mul_plainslot_single_map_ref(&cttmp1, &twozminone, hom)
//     ]
// }

// impl<'a, FC, Fg, const LOG: bool> BlindFoldPCS<'a, FC, Fg, LOG>
//     where FC: FoldableCode<R = Fg, C: LinearCode<R = Fg> + Clone>,
//           Fg: RingStore<Type: Field + FiniteRing> + Clone,
//           <SlotRing as RingStore>::Type: CanIsoFromTo<<Fg as RingStore>::Type>
// {
//     pub fn commit(&self, polycoeff: &[Ct], pk: &PublicKey) -> BlindFoldCommitment
//     {
//         BlindFoldCommitment{bcode_el: self.bfc.encode(polycoeff, pk)}
//     }

//     #[instrument(skip_all)]
//     pub fn eval(&self, bcom: &BlindFoldCommitment, z: &[El<Fg>], y: &Ct, polycoeff: &[Ct])
//         -> BlindFoldProof
//     {
//         let hom = self.bfc.iso().inv();
//         let d = self.bfc.foldablecode().d();
//         dbg!(d);

//         let mut proofcodes: Vec<Vec<Ct>> = Vec::with_capacity(d);
//         let mut topcode = &bcom.bcode_el;

//         let mut polys: Vec<Vec<Ct>> = Vec::with_capacity(d);
//         let cth = sumcheck_sum_blindfold(self.gbfv, self.field(), &hom,
//             polycoeff, z, &[], Some(self.gbfv.clone_ct(y)), None);
//         // let cth = sumcheck_sum_blindfold(self.gbfv, self.field(), &hom,
//         //     polycoeff, z, &[], None, None);
//         polys.push(cth);

//         let mut last: Vec<Ct> = Vec::with_capacity(
//             if self.bfc.foldablecode().k(0) == 1 {0} else {
//                 // TODO: allow code.generator().columns() to divide gbfv.pack()
//                 self.bfc.foldablecode().k(0)/self.gbfv.pack()});

//         let mut challvec: Vec<El<Fg>> = Vec::with_capacity(d - 1);

//         for dind in (0..d).rev() {
//             let chall = self.bf.get_challenge();

//             let leftscalars = self.bfc.foldablecode().t(dind).zip(self.denoms[dind].iter()).map(
//                 |(ti, di)| self.field().div(&self.field().add_ref(&chall, ti), &di));
//             let rightscalars = self.bfc.foldablecode().t(dind).zip(self.denoms[dind].iter()).map(
//                 |(ti, di)| self.field().div(&self.field().sub_ref(ti, &chall), &di));
//             let (leftcts, rightcts) = topcode.split_at(
//                 self.bfc.foldablecode().n(dind) / self.gbfv.pack());
//             let mut next_code = (0..leftcts.len()).map(|_| self.gbfv.ct_zero()).collect_vec();
//             self.gbfv.hom_add_assign_to(
//                 next_code.iter_mut(),
//                 self.gbfv.hom_mul_plain_map(leftcts, leftscalars, &hom).iter(),
//                 self.gbfv.hom_mul_plain_map(rightcts, rightscalars, &hom).iter()
//             );
//             proofcodes.push(next_code);
//             topcode = &proofcodes[d - 1 - dind];

//             challvec.insert(0, chall);
//             if dind != 0 {
//                 let tmpsum = univar_evaluate_at_fromctcoeff(self.gbfv, self.field(), &hom,
//                     &polys[d - 1 - dind], &challvec[0]);
//                 let cth = sumcheck_sum_blindfold(self.gbfv, self.field(), &hom,
//                     polycoeff, z, &challvec, Some(tmpsum), None);
//                 // let cth = sumcheck_sum_blindfold(self.gbfv, self.field(), &hom,
//                 //     polycoeff, z, &challvec, None, None);
//                 polys.push(cth);
//             }
//         }

//         // TODO: allow code.generator().columns() to divide gbfv.pack()
//         if self.bfc.foldablecode().k(0) > 1 {
//             last = multilinear_evaluate_at_fromctcoeff(self.gbfv, self.field(), &hom,
//                 polycoeff, &challvec);
//         }

//         BlindFoldProof {
//             bcode_els: proofcodes,
//             sumcheck_els: polys,
//             sumcheck_last: last
//         }
//     }

//     #[instrument(skip_all)]
//     pub fn verify(&self, bcom: BlindFoldCommitment, z: &[El<Fg>], y: El<Fg>,
//         polycoeff: Vec<Ct>, bproof: BlindFoldProof, sk: &SecretKey) -> bool
//     {
//         let toslotfield = self.iso();

//         let com = BaseFoldCommitment{code_el:
//             self.gbfv.dec_slots_map(bcom.bcode_el, sk, toslotfield).collect() };

//         let unipolyring = self.bf.get_unipolyring();
//         let proof = BaseFoldProof{
//             code_els: bproof.bcode_els.into_iter().map(|bcode|
//                 self.gbfv.dec_slots_map(bcode, sk, toslotfield).collect()).collect(),
//             sumcheck_els: bproof.sumcheck_els.into_iter().map(|ctcoeffs|
//                 unipolyring.from_terms(ctcoeffs.into_iter().enumerate().map(|(i, ctcoeff)|
//                     (toslotfield.map(self.gbfv.dec_slots_single_sum(ctcoeff, sk)), i)))
//                 ).collect(),
//             sumcheck_last: self.gbfv.dec_slots_map(bproof.sumcheck_last, sk, toslotfield).collect()
//         };

//         self.bf.reset_fs();
//         self.bf.verify(&com, z, y,
//             &self.gbfv.dec_slots_map(polycoeff, sk, toslotfield).collect_vec(), proof)
//     }
// }


#[cfg(test)]
mod tests {
    // use super::*;
    // use feanor_math::assert_el_eq;
    // use feanor_math::seq::VectorFn;
    // use feanor_math::rings::finite::FiniteRingStore;
    // use feanor_math::rings::poly::dense_poly::DensePolyRing;
    // use feanor_math::rings::multivariate::{
    //     MultivariatePolyRingStore, 
    //     multivariate_impl::MultivariatePolyRingImpl
    // };
    // use feanor_math::rings::extension::FreeAlgebraStore;
    // use proofs::util::gen_vector;
    // // use proofs::commit::basefold::sumcheck_sum_basefold;
    // use proofs::multilinear::{MultilinearBasis, sum_over_hypercube, from_hypercube_coeffs};
    // use easygbfv::{LOG, gbfv::SlotField, tests::get_gbfv_test};
    // use crate::util::tests::{test_correctness, test_correctness_ref};

    // #[test]
    // fn test_blindsumchecksum() {
        
    //     let gbfv = get_gbfv_test(0, 8, 200, None);
    //     let sk = gbfv.gen_sk();
    //     let slotring = gbfv.slot_ring();
    //     let slotfield = slotring.clone().as_field().ok().unwrap();
    //     let hom = gbfv.slot_ring().can_hom(&slotfield).unwrap();
    //     let unipolyring = DensePolyRing::new(slotfield.clone(), "X");

    //     let atzero_plus_atone = |mut inp: Vec<Ct>| {
    //         let c2 = gbfv.dec_slots_single_sum(inp.remove(2), &sk);
    //         let c1 = gbfv.dec_slots_single_sum(inp.remove(1), &sk);
    //         let c0 = gbfv.dec_slots_single_sum(inp.remove(0), &sk);
    //         let eval0 = slotring.clone_el(&c0);
    //         let eval1 = slotring.add(slotring.add(c0, c1), c2);
    //         slotring.add(eval0, eval1)
    //     };

    //     let N = 6;
    //     let polyring = MultivariatePolyRingImpl::new(slotfield.clone(), N);

    //     let coeffs = gen_vector::<El<SlotField>>(||
    //         slotfield.random_element(rand::random::<u64>), 1 << N);
    //     let ctin = gbfv.enc_slots_map_ref(coeffs.iter(), &hom, &sk);

    //     let mut poly = from_hypercube_coeffs(&polyring, &coeffs);
    //     let zvec = gen_vector::<El<SlotField>>(||
    //         slotfield.random_element(rand::random::<u64>), N);

    //     let eq = MultilinearBasis::new(&slotfield, &zvec).polynomial(&polyring);
    //     let bfpoly = polyring.mul_ref_fst(&poly, eq);
    //     let mut sumf = sum_over_hypercube(&polyring, &bfpoly, N, &[]);
    //     let mut sum = hom.map_ref(&sumf);

    //     let mut hd = sumcheck_sum_basefold(&unipolyring, &coeffs, &zvec, &[], Some(slotfield.clone_el(&sumf)));
    //     let mut cthd = sumcheck_sum_blindfold::<SlotField, LOG>(&gbfv, &slotfield, &hom,
    //         &ctin, &zvec, &[], None, Some(sumf));
    //     // let mut vec = (0..gbfv.pack()).map(|_| slotring.zero()).collect::<Vec<_>>();
    //     // vec[0] = slotring.clone_el(&sum);
    //     // let ctsum = gbfv.enc_slots_single(vec.into_iter(), &sk);
    //     // let mut cthd = sumcheck_sum_blindfold::<SlotField, LOG>(&gbfv, &slotfield, &hom,
    //     //     &ctin, &zvec, &[], Some(ctsum), None);
    //     // let mut cthd = sumcheck_sum_blindfold::<SlotField, LOG>(&gbfv, &slotfield, &hom,
    //     //     &ctin, &zvec, &[], None, None);

    //     // let ct_atzero = univar_evaluate_at_fromctcoeff(&gbfv, &slotfield, &hom, &cthd, &slotfield.zero());
    //     // let ct_atone = univar_evaluate_at_fromctcoeff(&gbfv, &slotfield, &hom, &cthd, &slotfield.one());
    //     // assert_el_eq!(slotring, dec_sum(gbfv.hom_add(&ct_atzero, &ct_atone)), &hom.map_ref(&sum));

    //     let mut rvec: Vec<El<SlotField>> = vec![];
    //     for ind in 1..=(N - gbfv.pack().ilog2() as usize - 1) {
    //         println!("Tested: {}", ind - 1);
    //         println!("Noise budget : {}", gbfv.noise_budget(&cthd, &sk));
    //         let r = slotfield.random_element(rand::random::<u64>);
    //         poly = polyring.specialize(&poly, N - ind,
    //             &polyring.create_term(slotfield.clone_el(&r),
    //                 polyring.create_monomial((0..N).map(|_| 0))));
    //         sumf = unipolyring.evaluate(&hd, &r, slotfield.identity());
    //         let ctsum = univar_evaluate_at_fromctcoeff(&gbfv, &slotfield, &hom, &cthd, &r);
    //         assert_el_eq!(slotring, &sum, atzero_plus_atone(gbfv.clone_cts(cthd.iter())));
    //         cthd.into_iter().enumerate().for_each(|(i, ctcoeff)| {
    //             assert_el_eq!(slotring,
    //                 hom.map_ref(unipolyring.coefficient_at(&hd, i)),
    //                 gbfv.dec_slots_single_sum(ctcoeff, &sk));
    //         });

    //         // sum = dec_sum(gbfv.clone_ct(&ctsum));
    //         sum = hom.map_ref(&sumf);

    //         rvec.insert(0, r);
    //         hd = sumcheck_sum_basefold(&unipolyring, &coeffs, &zvec, &rvec, Some(sumf));
    //         cthd = sumcheck_sum_blindfold::<SlotField, LOG>(&gbfv, &slotfield, &hom,
    //             &ctin, &zvec, &rvec, Some(ctsum), None);
    //         // cthd = sumcheck_sum_blindfold::<SlotField, LOG>(&gbfv, &slotfield, &hom,
    //         //     &ctin, &zvec, &rvec, None, None);
    //     }
    //     println!("Tested: {}", N - gbfv.pack().ilog2() as usize - 1);
    //     println!("Noise budget : {}", gbfv.noise_budget(&cthd, &sk));
    //     assert_el_eq!(slotring, &sum, atzero_plus_atone(gbfv.clone_cts(cthd.iter())));
    //     cthd.into_iter().enumerate().for_each(|(i, ctcoeff)| {
    //         assert_el_eq!(slotring,
    //             hom.map_ref(unipolyring.coefficient_at(&hd, i)),
    //             gbfv.dec_slots_single_sum(ctcoeff, &sk));
    //     });
    // }

    // #[test]
    // fn test_blindfoldcom() {

    //     let gbfv = get_gbfv_test(0, 8, 200, None);
    //     let sk = gbfv.gen_sk();
    //     let pk = gbfv.gen_pk(&sk);
    //     let slotfield = gbfv.slot_ring().clone().as_field().ok().unwrap();

    //     let k0 = gbfv.pack();
    //     let N = 6;
    //     let c = 2;
    //     let bf = BaseFoldPCS::new(&slotfield, N, k0, c, 100);

    //     let coeffs = gen_vector::<El<SlotField>>(||
    //         slotfield.random_element(rand::random::<u64>), 1 << N);
    //     let com = bf.commit(&coeffs);

    //     let bfc = BlindFoldableCode::new(&gbfv, bf.code());
    //     let bfold = BlindFoldPCS::new(&gbfv, bfc, &bf);
    //     let hom = bfold.bfc.bcode().iso().inv();

    //     let ctin = gbfv.enc_slots_map_ref(coeffs.iter(), &hom, &sk);

    //     let bcom = bfold.commit(&ctin, &pk);

    //     println!("Noise budget after blind encoding: {}", gbfv.noise_budget(&bcom.bcode_el, &sk));

    //     test_correctness(&gbfv, &slotfield, &sk, bcom.bcode_el, com.code_el, &hom);
    // }

    // #[test]
    // fn test_blindfoldeval() {
        
    //     let gbfv = get_gbfv_test(0, 8, 200, None);
    //     let sk = gbfv.gen_sk();
    //     let pk = gbfv.gen_pk(&sk);
    //     let slotfield = gbfv.slot_ring().clone().as_field().ok().unwrap();

    //     // TODO: remove redundancy in tests
    //     let k0 = gbfv.pack();
    //     let N = 6;
    //     let c = 2;
    //     let bf = BaseFoldPCS::new(&slotfield, N, k0, c, 100);
    //     let unipolyring = bf.get_unipolyring();

    //     let coeffs = gen_vector::<El<SlotField>>(||
    //         slotfield.random_element(rand::random::<u64>), 1 << N);
    //     let poly = from_hypercube_coeffs(bf.polyring(), &coeffs);
    //     let zinner = gen_vector::<El<SlotField>>(||
    //         slotfield.random_element(rand::random::<u64>), N);
    //     let z = (0..N).map_fn(|i| slotfield.clone_el(&zinner[i]));
    //     let y = bf.polyring().evaluate(&poly, &z, slotfield.identity());
    //     let zvec: Vec<_> = z.into_iter().collect();

    //     let com = bf.commit(&coeffs);
    //     let proof = bf.eval_fast(&com, &zvec, slotfield.clone_el(&y), &coeffs);

    //     assert!(bf.verify(&com, &zvec, slotfield.clone_el(&y), &coeffs,
    //         proof.clone(&slotfield, &unipolyring)));

    //     bf.reset_fs();

    //     let bfc = BlindFoldableCode::new(&gbfv, bf.code());
    //     let bfold = BlindFoldPCS::new(&gbfv, bfc, &bf);
    //     let hom = bfold.bfc.bcode().iso().inv();
    //     let ctin = gbfv.enc_slots_map_ref(coeffs.iter(), &hom, &sk);

    //     let bcom = bfold.commit(&ctin, &pk);
    //     let cty = gbfv.enc_firstslot_map_ref(&y, &hom, &sk);
    //     let bproof = bfold.eval(&bcom, &zvec, &cty, &ctin);

    //     for (bcode, code) in bproof.bcode_els.into_iter().zip(proof.code_els.iter()) {
    //         println!("Noise budget after blind folding: {}", gbfv.noise_budget(&bcode, &sk));
    //         test_correctness_ref(&gbfv, &slotfield, &sk, bcode, &code, &hom);
    //     }

    //     let slotring = gbfv.slot_ring();
    //     for (bpoly, poly) in bproof.sumcheck_els.into_iter().zip(proof.sumcheck_els.iter()) {
    //         println!("Noise budget after blind sumcheck: {}", gbfv.noise_budget(&bpoly, &sk));
    //         let deg = unipolyring.degree(&poly).unwrap();
    //         assert!(deg + 1 == bpoly.len());
    //         (0..deg).map(|i| unipolyring.coefficient_at(&poly, i)).zip(
    //             bpoly.into_iter().map(|ctcoeff| gbfv.dec_slots_single_sum(ctcoeff, &sk))
    //         ).for_each(|(coeff, coeff_fromct)|
    //             assert_el_eq!(slotring, hom.map_ref(coeff), coeff_fromct));
    //     }

    //     println!("Noise budget for last: {}", gbfv.noise_budget(&bproof.sumcheck_last, &sk));
    //     test_correctness_ref(&gbfv, &slotfield, &sk, bproof.sumcheck_last,
    //         &proof.sumcheck_last, &hom);
    // }

    // #[test]
    // fn test_blindfoldverify() {

    //     let gbfv = get_gbfv_test(0, 8, 200, None);
    //     let sk = gbfv.gen_sk();
    //     let pk = gbfv.gen_pk(&sk);
    //     let slotfield = gbfv.slot_ring().clone().as_field().ok().unwrap();

    //     let k0 = gbfv.pack();
    //     let N = 6;
    //     let c = 2;
    //     let bf = BaseFoldPCS::new(&slotfield, N, k0, c, 100);

    //     let coeffs = gen_vector::<El<SlotField>>(||
    //         slotfield.random_element(rand::random::<u64>), 1 << N);
    //     let poly = from_hypercube_coeffs(bf.polyring(), &coeffs);
    //     let zinner = gen_vector::<El<SlotField>>(||
    //         slotfield.random_element(rand::random::<u64>), N);
    //     let z = (0..N).map_fn(|i| slotfield.clone_el(&zinner[i]));
    //     let y = bf.polyring().evaluate(&poly, &z, slotfield.identity());

    //     let bfc = BlindFoldableCode::new(&gbfv, bf.code());
    //     let bfold = BlindFoldPCS::new(&gbfv, bfc, &bf);
    //     let hom = bfold.iso().inv();
    //     let ctin = gbfv.enc_slots_map(coeffs.into_iter(), &hom, &sk);

    //     let bcom = bfold.commit(&ctin, &pk);

    //     let zvec: Vec<_> = z.into_iter().collect();
    //     let cty = gbfv.enc_firstslot_map_ref(&y, &hom, &sk);
    //     let bproof = bfold.eval(&bcom, &zvec, &cty, &ctin);

    //     assert!(bfold.verify(bcom, &zvec, y, gbfv.clone_cts(ctin.iter()), bproof, &sk));
    // }
}
