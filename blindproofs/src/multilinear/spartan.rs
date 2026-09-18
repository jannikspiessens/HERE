use itertools::{izip, Itertools};
use std::cell::RefCell;

use feanor_math::rings::multivariate::MultivariatePolyRingStore;
use feanor_math::field::Field;
use feanor_math::ring::{El, RingStore};
use feanor_math::homomorphism::{CanIsoFromTo, Homomorphism};
use feanor_math::rings::finite::FiniteRing;

use easygbfv::{
    gbfv::{
        Ciphertext as Ct,
        GBFV,
        SlotRing,
        SecretKey, PublicKey
    },
};
use proofs::{
    codes::foldablecodes::{FoldableCode, DFC},
    basefold::{DPCS, MultilinearPCS},
    util::gen_vector,
    spartan::{
        SpartanPIOP, SpartanRowcheck, SpartanLincheck,
        SpartanRowcheckBase, SpartanLincheckBase
    },
    multilinear::{
        sumcheck::{Sumcheck, SumcheckBase},
        evaluate_at_fromcoeff,
    }
};
use crate::{
    util::VERIFY,
    codes::foldablecodes::BlindFoldableCode,
    basefold::{
        BlindFoldPCS, BlindFoldCommitment,
    },
    multilinear::{
        sumcheck::{BlindSumcheck, CTorPT},
        ctcoeffs_to_ctevals
    }
};

pub struct BlindSpartanPIOP<'a, F, const LOG: bool>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    plain: SpartanPIOP<'a, DPCS<'a, F>>,
    logpack: usize,
    pk: &'a PublicKey<'a>,
    z: Vec<Ct>,
    zA: Vec<Ct>,
    zB: Vec<Ct>,
    zC: Vec<Ct>,
    bfold: BlindFoldPCS<'a, DFC<'a, F>, F, LOG>,
    zcoeff: Vec<Ct>,
    com: BlindFoldCommitment,
}

impl<'a, F, const LOG: bool> BlindSpartanPIOP<'a, F, LOG>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    pub fn from_plain(plain: SpartanPIOP<'a, DPCS<'a, F>>, bf: &'a DPCS<'a, F>,
        gbfv: &'a GBFV<LOG>, pk: &'a PublicKey, sk: &'a SecretKey) -> Self
    {
        let vc = bf.polyring().indeterminate_count();
        assert!(vc == plain.varcount_cols());
        assert!(bf.code().k(0) == gbfv.pack()); // for now
        
        let bfc = BlindFoldableCode::new(&gbfv, bf.code());
        let bfold = BlindFoldPCS::new(&gbfv, bfc, &bf);

        let hom = bfold.iso().inv();
        let logpack = gbfv.pack().ilog2() as usize;

        let [z, zA, zB, zC] = plain.get_zM();
        let z = gbfv.enc_slots_map_ref(z.borrow().iter(), &hom, sk);
       
        // TODO: SET THIS PROPERLY
        let deep = false;
        let zcoeff = ctcoeffs_to_ctevals(gbfv, logpack, vc - logpack, &z, pk, true, deep);
        let com = bfold.commit(&zcoeff, pk);

        let zA = gbfv.enc_slots_map_ref(zA.borrow().iter(), &hom, sk);
        let zB = gbfv.enc_slots_map_ref(zB.borrow().iter(), &hom, sk);
        let zC = gbfv.enc_slots_map_ref(zC.borrow().iter(), &hom, sk);
        Self { plain, logpack, pk, z, zA, zB, zC, bfold, zcoeff, com }
    }

    pub fn execute(self, sk: &SecretKey) -> bool
    {
        let rowchecksum = Some(CTorPT::PT(self.bfold.get_gbfv().slot_ring().zero()));
        let browcheck = BlindSpartanRowcheck::new(self);
        if let Some((rX, evals)) = browcheck.execute(rowchecksum, sk) {
            browcheck.check_eval(evals, rX, sk) 
        } else { false }
    }
}


pub struct BlindSpartanRowcheck<'a, F, const LOG: bool>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    plain: SpartanRowcheck<'a, DPCS<'a, F>>,
    logpack: usize,
    pk: &'a PublicKey<'a>,
    wsz: Vec<Ct>,
    wszA: RefCell<Vec<Ct>>,
    wszB: RefCell<Vec<Ct>>,
    wszC: RefCell<Vec<Ct>>,
    bfold: BlindFoldPCS<'a, DFC<'a, F>, F, LOG>,
    zcoeff: Vec<Ct>,
    com: BlindFoldCommitment
}

impl<'a, F, const LOG: bool> BlindSpartanRowcheck<'a, F, LOG>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    pub fn new(bpiop: BlindSpartanPIOP<'a, F, LOG>) -> Self
    {
        let wszA = RefCell::new(bpiop.zA);
        let wszB = RefCell::new(bpiop.zB);
        let wszC = RefCell::new(bpiop.zC);
        let plain = SpartanRowcheck::for_piop(bpiop.plain);
        Self {
            plain,
            logpack: bpiop.logpack, pk: bpiop.pk,
            wsz: bpiop.z,
            wszA, wszB, wszC,
            bfold: bpiop.bfold, zcoeff: bpiop.zcoeff, com: bpiop.com
        }
    }
}

impl<'a, F, const LOG: bool> BlindSumcheck<3, LOG> for BlindSpartanRowcheck<'a, F, LOG>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    type SCB = SpartanRowcheckBase<'a, DPCS<'a, F>>;

    fn logpack(&self) -> usize {
        self.logpack
    }

    fn get_gbfv(&self) -> &GBFV<LOG> {
        &self.bfold.get_gbfv()
    }

    fn get_pk(&self) -> &PublicKey<'_> {
        self.pk
    }

    fn get_base(&self) -> &Self::SCB {
        self.plain.get_base()
    }

    fn compute_term_pt(ring: &F, atct: Vec<&El<F>>, _atpt: Option<&El<F>>, scalar: &El<F>) -> El<F>
    {
        SpartanRowcheck::<DPCS<F>>::compute_term(ring, core::array::from_fn(|i| atct[i]), scalar)
    }

    fn get_workspace_ct(&self) -> Vec<&RefCell<Vec<Ct>>> {
        vec![&self.wszA, &self.wszB, &self.wszC]
    }

    fn get_workspace_pt(&self) -> Option<&RefCell<Vec<El<F>>>> {
        None
    }

    fn getN() -> usize {
        3
    }

    fn avoid_automorphisms() -> bool {
        true
    }
    
    fn compute_term<I, J>(gbfv: &GBFV<LOG>, pk: &PublicKey,
        atct: Vec<&Ct>, _atpt: I, scalars: J) -> Ct
        where I: Iterator<Item = Option<El<SlotRing>>>, J: Iterator<Item = El<SlotRing>>
    {
        gbfv.hom_mul_plain_single(
            &gbfv.hom_sub(&gbfv.hom_mul_ref(atct[0], atct[1], pk), atct[2]), scalars)
    }

    fn check_eval(self, evals: Option<Vec<Vec<El<F>>>>, rX: Vec<El<F>>, sk: &SecretKey) 
        -> bool
    {
        let ring = self.get_base().field();
        let ranlen = if Self::avoid_automorphisms() { 1 << self.logpack() } else { 1 };
        let rA = gen_vector::<El<F>>(|| self.get_base().get_challenge(), ranlen);
        let rB = gen_vector::<El<F>>(|| self.get_base().get_challenge(), ranlen);
        let rC = gen_vector::<El<F>>(|| self.get_base().get_challenge(), ranlen);

        assert!(VERIFY == evals.is_some());
        assert!(VERIFY == true); // TODO: remove this assumption such that blincheck.execute
                                 // receives a CTorPT::CT

        let mut evals = evals.unwrap();
        let vzC = evals.pop().unwrap();
        let vzB = evals.pop().unwrap();
        let vzA = evals.pop().unwrap();
        let linchecksum = izip!(rA.iter(), rB.iter(), rC.iter(), vzA, vzB, vzC).fold(ring.zero(),
            |acc, (rAi, rBi, rCi, vzAi, vzBi, vzCi)| ring.add(acc,
                SpartanLincheck::<DPCS<F>>::compute_start(ring, rAi, rBi, rCi, vzAi, vzBi, vzCi)));
        let iso = self.bfold.get_gbfv().slot_ring().can_iso(ring).unwrap();
        let toslotring = iso.inv();
        let ptlinchecksum = Some(CTorPT::PT(toslotring.map(linchecksum)));
        let blincheck = BlindSpartanLincheck::new(self, &rA, &rB, &rC, rX);

        if let Some((rY, newevals)) = blincheck.execute(ptlinchecksum, sk) {
            blincheck.check_eval(newevals, rY, sk)
        } else { false }
    }
}

pub struct BlindSpartanLincheck<'a, F, const LOG: bool>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    plain: SpartanLincheck<'a, DPCS<'a, F>>,
    logpack: usize,
    pk: &'a PublicKey<'a>,
    wsz: RefCell<Vec<Ct>>,
    bfold: BlindFoldPCS<'a, DFC<'a, F>, F, LOG>,
    zcoeff: Vec<Ct>,
    com: BlindFoldCommitment
}

impl<'a, 'b, F, const LOG: bool> BlindSpartanLincheck<'a, F, LOG>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    pub fn new(rowcheck: BlindSpartanRowcheck<'a, F, LOG>, rA: &[El<F>], rB: &[El<F>], rC: &[El<F>],
        rX: Vec<El<F>>) -> Self
    {
        // TODO: do this prettier
        let piop = rowcheck.plain.move_out();
        let plain = SpartanLincheck::for_piop(piop, rA, rB, rC, rX);
        Self {
            plain,
            logpack: rowcheck.logpack,
            pk: rowcheck.pk,
            wsz: RefCell::new(rowcheck.wsz),
            bfold: rowcheck.bfold, zcoeff: rowcheck.zcoeff, com: rowcheck.com
        }
    }
}

impl<'a, F, const LOG: bool> BlindSumcheck<2, LOG> for BlindSpartanLincheck<'a, F, LOG>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    type SCB = SpartanLincheckBase<'a, DPCS<'a, F>>;
    
    fn logpack(&self) -> usize {
        self.logpack
    }

    fn get_gbfv(&self) -> &GBFV<LOG> {
        &self.bfold.get_gbfv()
    }

    fn get_pk(&self) -> &PublicKey<'_> {
        self.pk
    }


    fn get_base(&self) -> &Self::SCB {
        self.plain.get_base()
    }

    fn compute_term_pt(ring: &F, atct: Vec<&El<F>>, atpt: Option<&El<F>>, scalar: &El<F>) -> El<F>
    {
        SpartanLincheck::<DPCS<F>>::compute_term(ring, [atct[0], atpt.unwrap()], scalar)
    }

    fn get_workspace_ct(&self) -> Vec<&RefCell<Vec<Ct>>> {
        vec![&self.wsz]
    }

    fn get_workspace_pt(&self) -> Option<&RefCell<Vec<El<F>>>> {
        Some(&self.plain.get_wsM())
    }

    fn getN() -> usize {
        1
    }
    
    fn avoid_automorphisms() -> bool {
        false
    }

    fn compute_term<I, J>(gbfv: &GBFV<LOG>, _pk: &PublicKey,
        atct: Vec<&Ct>, atpt: I, _scalars: J) -> Ct
        where I: Iterator<Item = Option<El<SlotRing>>>, J: Iterator<Item = El<SlotRing>>
    {
        let atptu = atpt.into_iter().map(|el| el.unwrap());
        gbfv.hom_mul_plain_single(&atct[0], atptu)
    }

    fn check_eval(self, evals: Option<Vec<Vec<El<F>>>>, rX: Vec<El<F>>, sk: &SecretKey) -> bool
    {
        let ring = self.get_base().field();
        let gbfv = self.bfold.get_gbfv();

        assert!(VERIFY == evals.is_some());
        let y_opt = evals.map(|o| {
            let y = ring.clone_el(&o[0][0]);
            let zcoeffpt = gbfv.dec_slots(self.zcoeff.iter().map(|ct|
                gbfv.clone_ct(ct)).collect(), sk).collect_vec();
            let hom = self.bfold.iso().inv();
            let rXgbfv = rX.iter().map(|el| hom.map_ref(el)).collect_vec();
            let ev = evaluate_at_fromcoeff(gbfv.slot_ring(),
                self.get_base().varcount(), &rXgbfv, &zcoeffpt);
            debug_assert!(gbfv.slot_ring().eq_el(&hom.map_ref(&y), &ev[0]));
            y
        });
        let cty = {
            let evalz = self.get_workspace_ct()[0].borrow();
            debug_assert!(evalz.len() == 1);
            gbfv.clone_ct(&evalz[0])
        };
        let proof = self.bfold.eval(&self.com, &rX, &cty, &self.zcoeff);
        // println!("Noise budget: {}", proof.noise_budget(&gbfv, sk));

        if let Some(y) = y_opt {
            self.bfold.verify(self.com, &rX, y, self.zcoeff, proof, sk)
        } else { true }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::rings::extension::FreeAlgebraStore;
    use crate::util::get_gbfv;

    const VREP: usize = 100;

    #[test]
    fn test_blindspartan() {
        let gbfv = get_gbfv(400);
        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);
        let slotfield = gbfv.slot_ring().clone().as_field().ok().unwrap();

        let logpack = gbfv.pack().ilog2() as usize;
        let N = logpack + 3;

        let spartan = SpartanPIOP::random(&slotfield, N, N, VREP);

        let k0 = gbfv.pack();
        let c = 2;
        let bf = BaseFoldPCS::new(&slotfield, N, k0, c, VREP);

        let bspartan = BlindSpartanPIOP::from_plain(spartan, &bf, &gbfv, &pk, &sk);
        
        assert!(bspartan.execute(&sk))
    }
}

