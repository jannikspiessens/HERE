use itertools::{izip, Itertools};
use std::cell::RefCell;
use tracing::instrument;

use feanor_math::homomorphism::{CanHom, CanIso, CanIsoFromTo, Homomorphism};
use feanor_math::ring::{El, RingStore, RingExtension, RingExtensionStore};
use feanor_math::field::Field;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::seq::VectorFn;
use feanor_math::rings::zn::ZnRingStore;

use proofs::{
    util::ZZbig,
    multilinear::{
        evaluate_at_fromevals, evaluate_at_fromevals_inplace,
        sumcheck::{SumcheckBase, PolyEvals}
    },
};
use easygbfv::{
    gbfv::{
        GBFV, PublicKey, SecretKey,
        SlotRing, CiphertextRing,
        Ciphertext as Ct, CTCircuit
    }
};


trait BlindPolyEvaluator<F, const LOG: bool>
    where F: RingStore<Type: Field>,
        <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    fn sum01_sk(&self, gbfv: &GBFV<LOG>, sk: &SecretKey) -> El<SlotRing>;

    fn interp_sk(&self, a: &El<F>, field: &F,
        iso: &CanIso<&F, &SlotRing>, gbfv: &GBFV<LOG>, sk: &SecretKey) -> El<F>;
} 


pub struct BlindPolyEvals<const M: usize, const LOG: bool> {
    eval01: [Ct; 2],
    points: [i32; M],
    evals: [Ct; M],
}

impl<const M: usize, const LOG: bool> BlindPolyEvals<M, LOG>
{
    pub fn new(eval01: [Ct; 2], points: [i32; M], evals: [Ct; M]) -> Self
    { Self { eval01, points, evals } }

    pub fn clone(&self, gbfv: &GBFV<LOG>) -> Self {
        Self {
            eval01: core::array::from_fn(|i| gbfv.clone_ct(&self.eval01[i])),
            points: self.points,
            evals: core::array::from_fn(|i| gbfv.clone_ct(&self.evals[i]))
        }
    }

    fn at_zero(&self) -> &Ct {
        &self.eval01[0]
    }
    
    fn at_one(&self) -> &Ct {
        &self.eval01[1]
    }

    fn at_negone(gbfv: &GBFV<LOG>, atzero: &Ct, atone: &Ct) -> Ct {
        gbfv.hom_sub_single(gbfv.hom_add_single_ref(atzero, atzero), gbfv.clone_ct(atone))
    }

    fn at<'a, F>(&self, i: i32, field: &F,
        hom: &CanHom<&'a F, &'a SlotRing>, gbfv: &GBFV<LOG>) -> Ct
        where F: RingStore<Type: Field>,
            <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
    {
        match i {
            0 | 1 => gbfv.clone_ct(&self.eval01[i as usize]),
            -1 => BlindPolyEvals::<M, LOG>::at_negone(gbfv, self.at_zero(), self.at_one()),
            2 => BlindPolyEvals::<M, LOG>::at_negone(gbfv, self.at_one(), self.at_zero()),
            _ => {
                self.interp(&field.int_hom().map(i), field, hom, gbfv)
            }
        }
    }

    // TODO: redundant with PolyEvals?
    fn get_points(&self) -> impl Iterator<Item = &i32> {
        [0, 1].iter().chain(self.points.iter())
    }

    fn get_evals(&self) -> impl Iterator<Item = &Ct> {
        self.eval01.iter().chain(self.evals.iter())
    }

    #[instrument(skip_all)]
    pub fn interp<'a, F>(&self, a: &El<F>, field: &F,
        hom: &CanHom<&'a F, &'a SlotRing>, gbfv: &GBFV<LOG>) -> Ct
        where F: RingStore<Type: Field>,
            <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
    {
        let points = self.get_points().collect_vec();
        let lagr = PolyEvals::<F, M>::get_lagrange_polys_at(field, a, &points);
        self.get_evals().zip(lagr).fold(gbfv.ct_zero(), |acc, (e, l)| {
            gbfv.hom_add_single(acc, gbfv.hom_mul_plainslot_single_map(e, l, hom))
        })
    }

    pub fn print_sk(&self, gbfv: &GBFV<LOG>, sk: &SecretKey) {
        self.get_evals().for_each(|eval| gbfv.println_slots_sum(eval, sk))
    }

    pub fn pack(self, gbfv: &GBFV<LOG>, pk: &PublicKey, circuit: &CTCircuit)
        -> BlindPolyEvalsPacked<M, LOG>
    {
        let cts = self.eval01.into_iter().chain(self.evals.into_iter()).collect_vec();
        BlindPolyEvalsPacked {
            eval: gbfv.evaluate_circuit_small(circuit, &cts, pk).pop().unwrap(),
            points: self.points
        }
    }
}

impl<F, const M: usize, const LOG: bool> BlindPolyEvaluator<F, LOG> for BlindPolyEvals<M, LOG>
    where F: RingStore<Type: Field>,
        <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    fn sum01_sk(&self, gbfv: &GBFV<LOG>, sk: &SecretKey) -> El<SlotRing> {
        let sr = gbfv.slot_ring();
        [0, 1].into_iter().fold(sr.zero(), |acc, i|
             sr.add(acc, gbfv.dec_slots_single_sum(gbfv.clone_ct(&self.eval01[i as usize]), sk)))
    }


    fn interp_sk(&self, a: &El<F>, field: &F,
        iso: &CanIso<&F, &SlotRing>, gbfv: &GBFV<LOG>, sk: &SecretKey) -> El<F>
        where F: RingStore<Type: Field>,
            <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
    {
        let mut eval01_iter = self.eval01.iter().map(|ct|
            iso.map(gbfv.dec_slots_single_sum(gbfv.clone_ct(ct), sk)));
        let mut evals_iter = self.evals.iter().map(|ct|
            iso.map(gbfv.dec_slots_single_sum(gbfv.clone_ct(ct), sk)));
        PolyEvals::new(
            core::array::from_fn(|_| eval01_iter.next().unwrap()),
            self.points,
            core::array::from_fn(|_| evals_iter.next().unwrap()),
        ).interp(field, a)
    }
}


pub struct BlindPolyEvalsPacked<const M: usize, const LOG: bool> {
    eval: Ct,
    points: [i32; M]
}

impl<const M: usize, const LOG: bool> BlindPolyEvalsPacked<M, LOG> {
    fn modswitch(self, gbfv_ms: &GBFV<LOG>, old_ctring: &CiphertextRing) -> Self {
        Self { eval: gbfv_ms.mod_switch_ct(self.eval, old_ctring), points: self.points }
    }
}

impl<F, const M: usize, const LOG: bool> BlindPolyEvaluator<F, LOG>
    for BlindPolyEvalsPacked<M, LOG>
    where F: RingStore<Type: Field>,
        <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    fn sum01_sk(&self, gbfv: &GBFV<LOG>, sk: &SecretKey) -> El<SlotRing> {
        gbfv.dec_slots_single(gbfv.clone_ct(&self.eval), sk).take(2).fold(
            gbfv.slot_ring().zero(), |acc, x| gbfv.slot_ring().add(acc, x))
    }

    fn interp_sk(&self, a: &El<F>, field: &F,
        iso: &CanIso<&F, &SlotRing>, gbfv: &GBFV<LOG>, sk: &SecretKey) -> El<F>
        where F: RingStore<Type: Field>,
            <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
    {
        let mut evals = gbfv.dec_slots_single_map(gbfv.clone_ct(&self.eval), sk, iso);
        PolyEvals::new(
            core::array::from_fn(|_| evals.next().unwrap()),
            self.points,
            core::array::from_fn(|_| evals.next().unwrap()),
        ).interp(field, a)
    }
}


pub enum CTorPT {
    CT(Ct),
    PT(El<SlotRing>)
}

impl CTorPT {
    pub fn clone<const LOG: bool>(&self, gbfv: &GBFV<LOG>) -> Self {
        match self {
            CTorPT::CT(ct) => CTorPT::CT(gbfv.clone_ct(ct)),
            CTorPT::PT(pt) => CTorPT::PT(gbfv.slot_ring().clone_el(pt))
        }
    }
    
    pub fn eq_el<const LOG: bool>(&self, el: &El<SlotRing>, gbfv: &GBFV<LOG>, sk: &SecretKey)
        -> bool
    {
        match self {
            CTorPT::CT(ct) => gbfv.slot_ring().eq_el(
                &gbfv.dec_slots_single_sum(gbfv.clone_ct(ct), sk), el),
            CTorPT::PT(pt) => gbfv.slot_ring().eq_el(el, pt)
        }
    }

    pub fn unwrap_ct(self) -> Ct {
        match self {
            CTorPT::CT(ct) => ct,
            CTorPT::PT(_) => panic!("called `CTorPT::unwrap_ct()` on a `PT` value")
        }
    }

    pub fn unwrap_pt(self) -> El<SlotRing> {
        match self {
            CTorPT::CT(_) => panic!("called `CTorPT::unwrap_pt()` on a `CT` value"),
            CTorPT::PT(pt) => pt
        }
    }
}


// assert!(!msdata.is_some() || packcircuit.is_some())
pub struct BlindSumcheckCompressData<'a, const LOG: bool> {
    pub packcircuit: Option<CTCircuit>,
    pub msdata: Option<BlindSumcheckMSData<'a, LOG>>
}

pub struct BlindSumcheckMSData<'a, const LOG: bool> {
    pub gbfv_ms: &'a GBFV<LOG>,
    pub old_ctring: &'a CiphertextRing,
    pub sk_ms: Option<&'a SecretKey>
}

pub struct BlindSumcheckVerifierData<'a> {
    pub sk: &'a SecretKey,
    pub sum: El<SlotRing>
}


// type alias used below
type SCF<T, const D: usize, const LOG: bool> = <<T as BlindSumcheck<D, LOG>>::SCB as SumcheckBase<D>>::F;


// D: degree of the product sumcheck
// TODO: N: number of encrypted generic multilinear polynomials in the product sumcheck
// TODO: M: number of plaintext generic multilinear polynomials in the product sumcheck
pub trait BlindSumcheck<const D: usize, const LOG: bool>
    where [(); D - 1]: , <SlotRing as RingStore>::Type:
        CanIsoFromTo<<SCF<Self,D,LOG> as RingStore>::Type>
{
    type SCB: SumcheckBase<D>;

    fn getN() -> usize;
    fn avoid_automorphisms() -> bool;
    fn get_verifier_data(&self) -> Option<&BlindSumcheckVerifierData<'_>>;
    fn get_compress_data(&self) -> &BlindSumcheckCompressData<'_, LOG>;

    fn logpack(&self) -> usize;
    fn get_gbfv(&self) -> &GBFV<LOG>;
    fn get_pk(&self) -> &PublicKey;
    
    fn get_base(&self) -> &Self::SCB;

    fn get_workspace_ct(&self) -> Vec<&RefCell<Vec<Ct>>>;

    fn get_reference_pt(&self) -> Option<&[El<SCF<Self,D,LOG>>]>;

    fn get_workspace_pt(&self) -> Option<&RefCell<Vec<El<SCF<Self,D,LOG>>>>>;

    fn get_workspace_pt_ctring(&self) -> Option<&RefCell<Vec<El<CiphertextRing>>>>;

    fn compute_term<I, J>(gbfv: &GBFV<LOG>, pk: &PublicKey,
        atct: Vec<&Ct>, atpt: I, atpt_ctring: Option<&El<CiphertextRing>>, scalars: J)-> Ct
        where I: Iterator<Item = Option<El<SlotRing>>>, J: Iterator<Item = El<SlotRing>>;

    fn compute_term_pt(ring: &SCF<Self,D,LOG>, atct: Vec<&El<SCF<Self,D,LOG>>>,
        atpt: Option<&El<SCF<Self,D,LOG>>>, scalar: &El<SCF<Self,D,LOG>>) -> El<SCF<Self,D,LOG>>;

    fn check_eval(self, evals: Option<Vec<Vec<El<SCF<Self,D,LOG>>>>>,
        eX: Vec<El<SCF<Self,D,LOG>>>, sk: Option<&SecretKey>) -> bool;

    #[instrument(skip_all)]
    fn compute_round<'a>(&self, hom: &CanHom<&'a SCF<Self,D,LOG>, &'a SlotRing>,
        challs: &[El<SCF<Self,D,LOG>>], sum: Option<CTorPT>) -> BlindPolyEvals<{D - 1}, LOG>
    {
        let pk = self.get_pk();
        let ring = self.get_base().field();
        let gbfv = self.get_gbfv();
        let ctring = gbfv.ciphertext_ring();
        let AA = Self::avoid_automorphisms();
        let N = Self::getN();
        let i = challs.len();
        let vc = self.get_base().varcount();
        let lp = self.logpack();
        debug_assert!(i < vc - lp || !AA);
        // log of length of plaintext ws when this function returns
        let logwslenpt = vc - i;
        // log of length of encrypted ws when this function returns
        let logwslen = (vc - lp).saturating_sub(i);
        let p = 1 << lp;

        if i > 0 {
            let mut ws = self.get_workspace_ct();
            debug_assert!(ws.iter().all(|v| v.borrow().len() == 1 << (logwslen + 1)
                || (v.borrow().len() == 1 && logwslenpt < lp)));

            ws.iter_mut().for_each(|wszM| {
                let mut wszMmut = wszM.borrow_mut();
                blindsumcheck_foldonce_inplace(gbfv, logwslenpt + 1,
                    &hom.map_ref(&challs[0]), &mut wszMmut, &pk);
                wszMmut.truncate(1 << logwslen);
            });

            if let Some(wspt) = self.get_workspace_pt() {
                let mut wsptmut = wspt.borrow_mut();
                if i == 1 {
                    let ptref = self.get_reference_pt().expect("No reference declared");
                    *wsptmut = evaluate_at_fromevals(ring, vc, &challs[..1], ptref);
                } else {
                    debug_assert!(wsptmut.len() == 1 << (logwslenpt + 1));
                    evaluate_at_fromevals_inplace(ring, logwslenpt + 1,
                        &challs[..1], &mut wsptmut);
                    wsptmut.truncate(1 << logwslenpt);
                }
            }

            if logwslenpt >= lp && let Some(wsptpt) = self.get_workspace_pt_ctring() {
                let mut wsptmut = wsptpt.borrow_mut();
                debug_assert!(wsptmut.len() == 1 << (logwslen + 1));
                blindsumcheck_foldonce_inplace_ctring(gbfv, logwslenpt + 1,
                    &hom.map_ref(&challs[0]), &mut wsptmut);
                wsptmut.truncate(1 << logwslen);
            }
        }
        {
            let ws = self.get_workspace_ct();
            debug_assert!(ws.iter().all(|v| v.borrow().len() == 1 << logwslen));
            if let Some(wspt) = self.get_workspace_pt() && i > 0 {
                debug_assert!(wspt.borrow().len() == 1 << logwslenpt);
            }
        }

        let mut hzero = gbfv.ct_zero();
        let mut hone = gbfv.ct_zero();
        let other_points = self.get_base().get_other_eval_points();
        let mut other_evals: [Ct; D - 1] = core::array::from_fn(|_| gbfv.ct_zero());

        let ws = self.get_workspace_ct();
        let mut wsmut = (0..N).map(|i| ws[i].borrow_mut()).collect_vec();
        let mut rotatedws = Vec::new();
        if logwslen == 0 {
            (0..N).for_each(|j| {
                rotatedws.push(gbfv.hom_rotate(
                    gbfv.clone_ct(&wsmut[j][0]), p - (1 << (logwslenpt - 1)), &pk))
            })
        }
        let half = 1 << logwslen.saturating_sub(1);
        let zipws = wsmut.iter_mut().flat_map(|wsi| {
            let (wsiz, wsio) = wsi.split_at_mut(half);
            [wsiz, wsio]
        }).collect_vec();

        let half = 1 << logwslen.saturating_sub(1);
        let wsptptopt = if logwslenpt <= lp { None }
            else { self.get_workspace_pt_ctring().map(|x| x.borrow()) };
        let wsptptref = wsptptopt.as_ref();
        let wsptpt = (0..half).map(move |j|
            (wsptptref.map(|e| &e[j]), wsptptref.map(|e| &e[j + half]))
        );
        
        // would be prettier
        // let zipws = wsmut.iter_mut().enumerate().flat_map(|(j, wsi)| {
        //     let (wsiz, wsio) = wsi.split_at_mut(half);
        //     if logwslen == 0 { [wsiz, &mut [rotatedws[j]]] } else { [wsiz, wsio] }
        // }).collect_vec();
        let scalarchnk = self.get_base().get_scalars(challs)
            .chain((0..(p.saturating_sub(half))).map(|_| (ring.zero(), ring.zero())))
            .chunks(p);

        let half = 1 << (logwslenpt - 1);
        let zero = ring.zero();
        let wsptopt = self.get_workspace_pt().map(|x| x.borrow());
        let wsptref = if i == 0 { self.get_reference_pt() }
            else { wsptopt.as_ref().map(|v| &***v) };
        let wsptchnk = (0..half).map(move |j|
            (wsptref.map(|e| &e[j]), wsptref.map(|e| &e[j + half])))
            .chain((0..(p.saturating_sub(half))).map(|_| (Some(&zero), Some(&zero))))
            .chunks(p);

        izip!(wsptchnk.into_iter(), scalarchnk.into_iter(), wsptpt).enumerate()
            .for_each(|(j, (wspti, sci, wsptpti))|
        {
            let (wsptzi, wsptoi): (Vec<_>, Vec<_>) = wspti.unzip();
            let (wsptptzi, wsptptoi) = wsptpti;
            let (sczi, scoi): (Vec<_>, Vec<_>) = sci.unzip();
            
            let wszi = (0..N).map(|k| &zipws[2*k][j]).collect_vec();
            gbfv.hom_add_assign_single(&mut hzero, &Self::compute_term(gbfv, pk,
                wszi,
                wsptzi.iter().map(|opt| opt.map(|el| hom.map_ref(el))),
                wsptptzi,
                sczi.iter().map(|el| hom.map_ref(el)))
            );

            if sum.is_none() {
                // let wsoi = (0..N).map(|k| &zipws[2*k+1][j]).collect_vec();
                let wsoi = if logwslen > 0 {
                    (0..N).map(|k| &zipws[2*k+1][j]).collect_vec()
                } else {
                    (0..N).map(|j| &rotatedws[j]).collect_vec()
                };
                gbfv.hom_add_assign_single(&mut hone, &Self::compute_term(gbfv, pk,
                    wsoi,
                    wsptoi.iter().map(|opt| opt.map(|el| hom.map_ref(el))),
                    wsptptoi,
                    scoi.iter().map(|el| hom.map_ref(el))
                ));
            }

            let sci_poly = sczi.into_iter().zip(scoi.into_iter()).map(|(z, o)|
                PolyEvals::<SCF<Self,D,LOG>, 0>::new(
                    [z, o], [], [])).collect_vec();
            let wspti_poly = wsptzi.into_iter().zip(wsptoi.into_iter()).map(|(z, o)| z.map(|zu| {
                let ou = o.unwrap();
                PolyEvals::<SCF<Self,D,LOG>, 0>::new(
                    [ring.clone_el(zu), ring.clone_el(ou)], [], [])
            })).collect_vec();
            // let wszoi = (0..2*N).map(|k| &zipws[k][j]).collect_vec();
            let wszoi = if logwslen > 0 {
                (0..2*N).map(|k| &zipws[k][j]).collect_vec()
            } else {
                (0..N).map(|k| &zipws[2*k][j]).interleave((0..N).map(|j| &rotatedws[j])).collect_vec()
            };
            other_evals.iter_mut().zip(other_points.iter()).for_each(|(eval, point)|
            {

                let wppptpti = {
                    let pointf = ring.int_hom().map(*point);
                    let lagr = PolyEvals::<SCF<Self,D,LOG>, 0>::get_lagrange_polys_at(ring,
                        &pointf, &[&0, &1]);
                    wsptptzi.map(|x|
                        [x, wsptptoi.unwrap()].into_iter().zip(lagr).fold(ctring.zero(),
                            |acc, (e, l)| ctring.add(acc,
                                ctring_mul_scalar(gbfv, e, hom.map(l)))))
                };

                let scpi = sci_poly.iter().map(|poly| hom.map(poly.at(ring, *point)));
                let wsppti = wspti_poly.iter().map(|poly|
                    poly.as_ref().map(|p| hom.map(p.at(ring, *point)))
                );
                let wspi = wszoi.iter().chunks(2).into_iter().map(|mut x| BlindPolyEvals::new(
                        core::array::from_fn(|_| gbfv.clone_ct(&x.next().unwrap())), [], []
                    ).at(*point, ring, hom, gbfv)
                ).collect::<Vec<_>>();
                debug_assert!(wspi.len() == N);
                let wspi_iter = wspi.iter();
                gbfv.hom_add_assign_single(eval, &Self::compute_term(gbfv, pk,
                    wspi_iter.collect_vec(), wsppti, wppptpti.as_ref(), scpi)
                );
            });
        });

        hone = if let Some(sum) = sum {
            match sum {
                CTorPT::CT(ct) => gbfv.hom_sub_single(ct, gbfv.clone_ct(&hzero)),
                CTorPT::PT(pt) => {
                    let tmp0neg = gbfv.hom_sub_single(gbfv.ct_zero(), gbfv.clone_ct(&hzero));
                    gbfv.hom_add_plain_single(tmp0neg,
                        gbfv.enc_firstslot(gbfv.slot_ring().clone_el(&pt)))
                }
            }
        } else { hone };
        BlindPolyEvals::new([hzero, hone], other_points, other_evals)
    }

    #[instrument(skip_all)]
    fn execute(&self, sum: Option<CTorPT>)
        -> Option<(Vec<El<SCF<Self,D,LOG>>>, Option<Vec<Vec<El<SCF<Self,D,LOG>>>>>)>
    {
        let ring = self.get_base().field();
        let lp = self.logpack();
        let gbfv = self.get_gbfv();
        let pk = self.get_pk();
        let slotring = gbfv.slot_ring();
        let mut challvec = Vec::new();

        let iso = slotring.can_iso(ring).unwrap();
        let hom = slotring.can_hom(ring).unwrap();

        let AA = Self::avoid_automorphisms();
        let offset = if AA { lp } else { 0 };

        let (sk, sum_v) = self.get_verifier_data().map(|o| (o.sk, &o.sum)).unzip();

        let cd = self.get_compress_data();
        let (gbfv_v, sk_v) = if let Some(msdata) = &cd.msdata {
            (msdata.gbfv_ms, msdata.sk_ms)
        } else { (gbfv, sk) };

        let mut tmpsum = sum;
        let rounds = self.get_base().varcount() - offset;
        if !(0..rounds).all(|i| {
            if LOG { println!("Blind Sumcheck ================== Round {i}") };
            // let hdi = self.compute_round(&hom, &challvec, None);
            let hdi = self.compute_round(&hom, &challvec, tmpsum.as_ref().map(|o| o.clone(gbfv)));

            let hdi_v: Box<dyn BlindPolyEvaluator<SCF<Self,D,LOG>, LOG>> =
                if let Some(circuit) = cd.packcircuit.as_ref() {
                    let mut tmp = hdi.clone(gbfv).pack(gbfv, pk, circuit);
                    if let Some(msdata) = &cd.msdata {
                        tmp = tmp.modswitch(msdata.gbfv_ms, msdata.old_ctring);
                    };
                    Box::new(tmp)
                } else {
                    Box::new(hdi.clone(gbfv))
                };

            let mut res = sk_v.is_none_or(|usk_v| {
                let hdi_sum_dec = hdi_v.sum01_sk(gbfv_v, usk_v);
                if i == 0 { slotring.eq_el(&hdi_sum_dec, &sum_v.unwrap()) }
                else { tmpsum.as_ref().unwrap().eq_el(&hdi_sum_dec, gbfv, sk.unwrap()) }
            });
            let chall = self.get_base().get_challenge();

            tmpsum = Some(CTorPT::CT(hdi.interp(&chall, ring, &hom, gbfv)));
            
            res &= sk_v.is_none_or(|usk_v| {
                let hdi_interp_dec = hdi_v.interp_sk(&chall, ring, &iso, gbfv_v, usk_v);
                tmpsum.as_ref().unwrap().eq_el(&hom.map(hdi_interp_dec), gbfv, sk.unwrap())
            });

            challvec.insert(0, chall);
            res
        }) { return None };

        // compute full evaluations (prover)
        if let Some(wspt) = self.get_workspace_pt() {
            let mut wsptmut = wspt.borrow_mut();
            evaluate_at_fromevals_inplace(ring, offset + 1, &challvec[..1], &mut wsptmut);
            wsptmut.truncate(1 << offset);
        }

        let mut ws = self.get_workspace_ct();
        ws.iter_mut().for_each(|wsi| {
            let mut wsimut = wsi.borrow_mut();
            blindsumcheck_foldonce_inplace(gbfv, offset + 1,
                &hom.map_ref(&challvec[0]), &mut wsimut, &pk)
        });
        let ws = (0..Self::getN()).map(|i| {
            let wsiref = ws[i].borrow();
            gbfv.clone_ct(&wsiref[0])
        }).collect_vec();

        let ws_dec = if sk.is_some() {
            let usk = sk.unwrap();
            let eX = tmpsum.unwrap().unwrap_ct();

            // get final evaluation (verifier)
            println!("Noise budget: {}", gbfv.noise_budget(&[gbfv.clone_ct(&eX)], usk));
            let eXpt = iso.map(gbfv.dec_slots_single_sum(eX, usk));

            // compute final scalar (verifier)
            let (mut sc, sco): (Vec<_>, Vec<_>) = self.get_base().get_scalars(&challvec).unzip();
            sc.extend(sco);

            let wsptopt = self.get_workspace_pt().map(|x| x.borrow());
            let wsptoptref = wsptopt.as_ref();

            // decrypt alleged multilinear polynomial evaluations (verifier)
            if AA == true {
                let tmp = (0..Self::getN()).map(|i|
                    gbfv.dec_slots_single_map(gbfv.clone_ct(&ws[i]), usk, &iso).collect_vec()
                ).collect_vec();
                debug_assert!(wsptoptref.is_none_or(|v| v.len() == 1 << lp));
                debug_assert!(sc.len() == 1 << lp);
                let rhs = sc.into_iter().enumerate().fold(ring.zero(), |acc, (i, sci)|
                    ring.add(acc, Self::compute_term_pt(ring,
                        (0..Self::getN()).map(|j| &tmp[j][i]).collect(),
                        wsptoptref.map(|un| &un[i]), &sci))
                );
                if !ring.eq_el(&eXpt, &rhs) { return None };
                Some(tmp)
            } else {
                let tmp = (0..Self::getN()).map(|i|
                    vec![iso.map(gbfv.dec_slots_single_sum(gbfv.clone_ct(&ws[i]), usk))]
                ).collect_vec();
                debug_assert!(wsptoptref.is_none_or(|v| v.len() == 1));
                let rhs = Self::compute_term_pt(ring,
                        (0..Self::getN()).map(|j| &tmp[j][0]).collect(),
                        wsptoptref.map(|un| &un[0]), &sc[0]);
                if !ring.eq_el(&eXpt, &rhs) { return None };
                Some(tmp)
            }
        } else { None };
        
        Some((challvec, ws_dec))
    }
}


#[instrument(skip_all)]
pub fn blindsumcheck_foldonce_inplace<const LOG: bool>(gbfv: &GBFV<LOG>, logsize: usize,
    chall: &El<SlotRing>, evals: &mut [Ct], pk: &PublicKey)
{
    let pack = gbfv.pack();
    let ring = gbfv.slot_ring();
    let zero = ring.zero();
    let zeroscalar = ring.sub_ref_snd(ring.one(), chall);
    if evals.len() % 2 == 0 {
        debug_assert!(evals.len()*pack == 1 << logsize);
        let (l, r) = evals.split_at_mut(evals.len() / 2);
        l.iter_mut().zip(r).for_each(|(li, ri)|
            *li = gbfv.hom_add_single(
                gbfv.hom_mul_plainslot_single_ref(li, &zeroscalar),
                gbfv.hom_mul_plainslot_single_ref(ri, chall)
            )
        );
    } else if evals.len() == 1 {
        debug_assert!(1 << logsize <= pack && logsize > 0);
        let half = 1 << (logsize - 1);
        let tmp = gbfv.clone_ct(&evals[0]);
        let l = gbfv.hom_mul_plain_single_ref(&tmp,
            (0..half).map(|_| &zeroscalar).chain((0..(pack - half)).map(|_| &zero)));
        // TODO: makes sense to first rotate right?
        let r = gbfv.hom_mul_plain_single_ref(&gbfv.hom_rotate(tmp, pack - half, &pk),
            (0..half).map(|_| chall).chain((0..(pack - half)).map(|_| &zero)));
        gbfv.hom_add_assign_to_single(&mut evals[0], &l, &r)
    } else {
        panic!("Length of input to blindsumcheck_foldonce_inplace must be a power of two.")
    }
}

#[instrument(skip_all)]
pub fn ctring_mul_scalar<const LOG: bool>(gbfv: &GBFV<LOG>,
    el: &El<CiphertextRing>, sc: El<SlotRing>) -> El<CiphertextRing>
{
    let slotring = gbfv.slot_ring();
    let slotring_fa = slotring.get_ring().clone().unwrap_self();
    let slotring_br = slotring_fa.base_ring();
    let ctring = gbfv.ciphertext_ring();

    let mut tmp = ctring.clone_el(el);
    ctring.get_ring().mul_assign_base_through_hom(&mut tmp,
        &slotring_br.smallest_lift(slotring_fa.wrt_canonical_basis(
            &slotring.get_ring().unwrap_element(sc)).at(0)),
        ctring.base_ring().can_hom(&ZZbig).unwrap()
    );
    tmp
}

#[instrument(skip_all)]
pub fn blindsumcheck_foldonce_inplace_ctring<const LOG: bool>(gbfv: &GBFV<LOG>, logsize: usize,
    chall: &El<SlotRing>, evals: &mut [El<CiphertextRing>])
{
    let pack = gbfv.pack();
    let ctring = gbfv.ciphertext_ring();
    let ring = gbfv.slot_ring();
    let zeroscalar = ring.sub_ref_snd(ring.one(), chall);
    if evals.len() % 2 == 0 {
        debug_assert!(evals.len()*pack == 1 << logsize);
        let (l, r) = evals.split_at_mut(evals.len() / 2);
        l.iter_mut().zip(r).for_each(|(li, ri)|
            *li = ctring.add(
                ctring_mul_scalar(gbfv, li, ring.clone_el(&zeroscalar)),
                ctring_mul_scalar(gbfv, ri, ring.clone_el(&chall)),
            )
        );
    } else {
        // TODO
        panic!("Length of input to blindsumcheck_foldonce_inplace_pt must be a power of two and larger than two.")
    }
}

// #[instrument(skip_all)]
// pub fn ptring_mul_scalar<const LOG: bool>(gbfv: &GBFV<LOG>,
//     el: &El<PlaintextRing>, sc: El<SlotRing>) -> El<PlaintextRing>
// {
//     let slotring = gbfv.slot_ring();
//     let slotring_fa = slotring.get_ring().clone().unwrap_self();
//     let slotring_br = slotring_fa.base_ring();
//     let ptring = gbfv.plaintext_ring();

//     let mut tmp = ptring.clone_el(el);
//     ptring.get_ring().mul_assign_base_through_hom(&mut tmp,
//         &slotring_br.smallest_lift(slotring_fa.wrt_canonical_basis(
//             &slotring.get_ring().unwrap_element(sc)).at(0)),
//         ptring.base_ring().can_hom(&ZZbig).unwrap()
//     );
//     tmp
// }

// #[instrument(skip_all)]
// pub fn blindsumcheck_foldonce_inplace_ptring<const LOG: bool>(gbfv: &GBFV<LOG>, logsize: usize,
//     chall: &El<SlotRing>, evals: &mut [El<PlaintextRing>])
// {
//     let pack = gbfv.pack();
//     let ptring = gbfv.plaintext_ring();
//     let ring = gbfv.slot_ring();
//     let zeroscalar = ring.sub_ref_snd(ring.one(), chall);
//     if evals.len() % 2 == 0 {
//         debug_assert!(evals.len()*pack == 1 << logsize);
//         let (l, r) = evals.split_at_mut(evals.len() / 2);
//         l.iter_mut().zip(r).for_each(|(li, ri)|
//             *li = ptring.add(
//                 ptring_mul_scalar(gbfv, li, ring.clone_el(&zeroscalar)),
//                 ptring_mul_scalar(gbfv, ri, ring.clone_el(&chall)),
//             )
//         );
//     } else {
//         panic!("Length of input to blindsumcheck_foldonce_inplace_pt must be a power of two and larger than two.")
//     }
// }


#[cfg(test)]
mod tests {
    // use super::*;

    // use rand::RngCore;
    // use rand_seeder::{Seeder, SipRng};

    // use feanor_math::rings::finite::FiniteRingStore;
    // use fheanor::number_ring::NumberRingQuotientStore;
    // use proofs::util::gen_vector;
    // use easygbfv::tests::get_gbfv_test;

    // #[test]
    // fn test_ctring_hom() {

    //     let gbfv = get_gbfv_test(0, 8, 120, None);
    //     let slotring = gbfv.slot_ring();
    //     let p = gbfv.pack();
        
    //     let mut rng: SipRng = Seeder::from("test").into_rng();
    //     let pt1 = gen_vector::<El<SlotRing>>(||
    //         slotring.random_element(|| rng.next_u64()), p);
    //     let pt2 = gen_vector::<El<SlotRing>>(||
    //         slotring.random_element(|| rng.next_u64()), p);
    //     let sc = slotring.random_element(|| rng.next_u64());

    //     let pta = pt1.iter().zip(pt2.iter()).map(|(l, r)| slotring.add_ref(l, r));
    //     let ptm = pt1.iter().zip(pt2.iter()).map(|(l, r)| slotring.mul_ref(l, r));
    //     let ptsc = pt1.iter().map(|el| slotring.mul_ref(el, &sc));

    //     let pt1_ctring = gbfv.lift_to_ctrin(&gbfv.encode_slots_single(pt1.iter().map(|el| slotring.clone_el(el))));
    //     let pt2_ctring = gbfv.lift_to_ctrin(&gbfv.encode_slots_single(pt2.iter().map(|el| slotring.clone_el(el))));
        
    //     let pta_ctring = gbfv.ciphertext_ring().add_ref(&pt1_ctring, &pt2_ctring);
    //     let ptsc_ctring = ctring_mul_scalar(&gbfv, &pt1_ctring, slotring.clone_el(&sc));
    //     let ptm_ctring = gbfv.ciphertext_ring().mul(pt1_ctring, pt2_ctring);

    //     // TODO: implement decode for ctring elements
    //     assert!(gbfv.decode_slots_single(pta_ctring).zip(pta).all(|(l,r)| slotring.eq_el(&l, &r)));
    //     assert!(gbfv.decode_slots_single(ptm_ctring).zip(ptm).all(|(l,r)| slotring.eq_el(&l, &r)));
    //     assert!(gbfv.decode_slots_single(ptsc_ctring).zip(ptsc).all(|(l, r)| slotring.eq_el(&l, &r)))
    // }

    // #[test]
    // fn test_ctring_rot() {

    //     let gbfv = get_gbfv_test(0, 8, 120, None);
    //     let slotring = gbfv.slot_ring();
    //     let ctring = gbfv.plaintext_ring();
    //     let p = gbfv.pack();
        
    //     let mut rng: SipRng = Seeder::from("test").into_rng();
    //     let mut pt = gen_vector::<El<SlotRing>>(|| slotring.random_element(|| rng.next_u64()), p);
    //     let pt_ctring = gbfv.encode_slots_single(pt.iter().map(|el| slotring.clone_el(el)));
        
    //     let by = p/2;
    //     let gby = gbfv.get_rot_galois_el(by);
    //     let pt_ctring_rot = ctring.apply_galois_action(&pt_ctring, &gby);

    //     pt.rotate_right(by);

    //     assert!(gbfv.decode_slots_single(pt_ctring_rot).zip(pt).all(|(l,r)| slotring.eq_el(&l, &r)))
    // }
}

