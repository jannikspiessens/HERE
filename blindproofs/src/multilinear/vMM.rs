use itertools::Itertools;
use std::cell::RefCell; use tracing::instrument;
use serde::Serialize;
use serde::de::DeserializeSeed;

use feanor_math::serialization::{SerializeWithRing, DeserializeWithRing};
use feanor_math::field::Field;
use feanor_math::ring::{El, RingStore};
use feanor_math::homomorphism::{CanIsoFromTo, Homomorphism};
use feanor_math::rings::{
    multivariate::MultivariatePolyRingStore,
    finite::FiniteRing
};

use feanor_serde::seq::{SerializableSeq, DeserializeSeedSeq};

use fheanor::cache::{ CachedDataKey, create_cached, SerializeDeserializeWith, StoreAs };

use easygbfv::{
    gbfv::{
        Ciphertext as Ct,
        GBFV, SlotRing, CiphertextRing,
        SecretKey, PublicKey,
        util::compress_circuit
    },
};

use proofs::{
    commit::{MultilinearPCS, DPCS},
    multilinear::{
        sumcheck::{Sumcheck, SumcheckBase},
        evaluate_at_fromevals, MultilinearBasisEvals,
        vMM::{
            vMMPIOP, vMMLincheck, vMMLincheckBase
        },
    },
    util::matmul::{MatrixMul, DenseMatrixMul}
};

use crate::{
    codes::foldablecodes::BlindFoldableCode,
    multilinear::sumcheck::{BlindSumcheck, ctring_mul_scalar,
        BlindSumcheckCompressData, BlindSumcheckVerifierData, BlindSumcheckMSData},
    commit::{DBPCS, basefold::BlindFoldPCS}
};


struct PTEncodedMatrix {
    pub matrix: Vec<El<CiphertextRing>>
}

impl PTEncodedMatrix
{
    fn key<'a, F, const LOG: bool>(gbfv: &GBFV<LOG>, M: &DenseMatrixMul<'a, F>) -> CachedDataKey
        where F: RingStore
    {
        let name = format!("{}_ctring_{}", M.desc(), gbfv.id_string());
        CachedDataKey::String(name.to_string())
    }

    fn new<'a, F, const LOG: bool>(gbfv: &GBFV<LOG>, field: &F, M: &DenseMatrixMul<'a, F>) -> Self
        where F: RingStore, <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
    {
        let hom = gbfv.slot_ring().can_hom(field).unwrap();
        let matrix = M.data().chunks_exact(M.columns()).flat_map(|Mrow|
            Mrow.chunks_exact(gbfv.pack()).map(|ptels|
            gbfv.lift_to_ctring(
                &gbfv.encode_slots_single(ptels.into_iter().map(|ptel| hom.map_ref(ptel))))
        )).collect();
        Self { matrix }
    }
}

impl SerializeDeserializeWith<CiphertextRing> for PTEncodedMatrix
{
    fn deserialize_with_data<'de, D: serde::Deserializer<'de>>(data: CiphertextRing, deserializer: D) -> Result<Self, D::Error> {
        DeserializeSeedSeq::new(
            std::iter::repeat(DeserializeWithRing::new(&data)),
            Vec::new(),
            |mut current, next| { current.push(next); current }
        ).deserialize(deserializer).map(|v| PTEncodedMatrix{ matrix: v})
    }

    fn serialize_with_data<S: serde::Serializer>(&self, data: &CiphertextRing, serializer: S) -> Result<S::Ok, S::Error> {
        SerializableSeq::new(self.matrix.iter().map(|ptel|
            SerializeWithRing::new(ptel, data))).serialize(serializer)
    }
}


pub struct BlindvMMPIOP<'a, F, const LOG: bool>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    plain: vMMPIOP<'a, DPCS<'a, F>>,
    vc: usize,
    logpack: usize,
    pk: &'a PublicKey,
    z: RefCell<Vec<Ct>>,
    M: PTEncodedMatrix,
    bfold: DBPCS<'a, F, LOG>,
}

impl<'a, F, const LOG: bool> BlindvMMPIOP<'a, F, LOG>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    #[instrument(skip_all)]
    pub fn from_plain(plain: vMMPIOP<'a, DPCS<'a, F>>, bf: &'a DPCS<'a, F>,
        gbfv: &'a GBFV<LOG>, pk: &'a PublicKey, z: Vec<Ct>,
    ) -> Self
    {
        let vc = bf.polyring().indeterminate_count();
        assert!(vc == plain.varcount_cols());
        
        let bfc = BlindFoldableCode::new(&gbfv, bf.code());
        let bfold = BlindFoldPCS::new(&gbfv, bfc, &bf);

        let logpack = gbfv.pack().ilog2() as usize;

        // encoding of matrix (can not use encoding of matrix used for matmul circuit)
        let key = PTEncodedMatrix::key(gbfv, plain.matrix());
        let M = create_cached::<_, _, _, LOG>(gbfv.ciphertext_ring().clone(),
            || PTEncodedMatrix::new(gbfv, plain.field(), plain.matrix()),
            &[key], Some(gbfv.cache_dir()), StoreAs::AlwaysJson);

        Self { plain, logpack, vc, pk, z: RefCell::new(z), M, bfold }
    }

    #[instrument(skip_all)]
    pub fn execute(&'a self, pre_encode: bool, bscmsd: Option<BlindSumcheckMSData<'a, LOG>>,
        sk: Option<&'a SecretKey>) -> bool
    {
        let blincheck = BlindvMMLincheck::new(self, pre_encode, bscmsd, sk);
        // NOTE: one could compute zMtau from zM but why would you?
        if let Some((rX, evals)) = blincheck.execute(None) {
            blincheck.check_eval(evals, rX, sk) 
        } else { false }
    }

    // this is an overestimation for the PCS (no pruning)
    // also does not take into account ring-switching
    pub fn proofsize(&self, gbfv_ms: Option<&GBFV<LOG>>) -> u64 {
        let gbfv = gbfv_ms.unwrap_or(self.bfold.get_gbfv());
        self.bfold.get_plain().proofsize() as u64
            + gbfv.ct_size()*(self.plain.varcount_cols() as u64)
    }
}


pub struct BlindvMMLincheck<'a, F, const LOG: bool>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    plain: vMMLincheck<'a, DPCS<'a, F>>,
    logpack: usize,
    pk: &'a PublicKey,
    tauM: Option<RefCell<Vec<El<CiphertextRing>>>>,
    wsz: RefCell<Vec<Ct>>,
    bfold: &'a DBPCS<'a, F, LOG>,
    bscvd: Option<BlindSumcheckVerifierData<'a>>,
    bsccd: BlindSumcheckCompressData<'a, LOG>
}

impl<'a, 'b, F, const LOG: bool> BlindvMMLincheck<'a, F, LOG>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    #[instrument(skip_all)]
    pub fn new(bpiop: &'a BlindvMMPIOP<'a, F, LOG>, pre_encode: bool,
        bscmsd: Option<BlindSumcheckMSData<'a, LOG>>, sk: Option<&'a SecretKey>)
        -> Self
    {
        let field = bpiop.plain.field();
        let gbfv = bpiop.bfold.get_gbfv();
        let toslotring = gbfv.slot_ring().can_hom(field).unwrap();
        let tauM = pre_encode.then(|| {
            let ctring = gbfv.ciphertext_ring();

            let eqevals = MultilinearBasisEvals::new(field, &bpiop.plain.tau());

            let mut tmp = (0..(1 << bpiop.vc)/gbfv.pack()).map(|_| ctring.zero()).collect_vec();

            let packcols = bpiop.plain.matrix().columns()/gbfv.pack();
            bpiop.M.matrix.chunks_exact(packcols).zip(eqevals).for_each(|(Mrow, eqi)|
                Mrow.iter().zip(tmp.iter_mut()).for_each(|(Mj, rj)|
                    ctring.add_assign(rj, ctring_mul_scalar(gbfv, &Mj, toslotring.map_ref(&eqi)))
                )
            );
            RefCell::new(tmp)
        });
    
        let bscvd = sk.map(|usk| BlindSumcheckVerifierData {
            sk: usk,
            sum: toslotring.map_ref(bpiop.plain.zMtau())
        });

        // TODO: make bool param for depth of circuit
        let packcircuit = Some(gbfv.read_or_create_circuit(gbfv.ciphertext_ring(),
            "compress_lifted", || gbfv.lift_circuit(compress_circuit::<true, _>(gbfv, 3))));
        let bsccd = BlindSumcheckCompressData { packcircuit, msdata: bscmsd };

        let plain = vMMLincheck::for_piop(&bpiop.plain);

        Self {
            plain,
            logpack: bpiop.logpack,
            pk: bpiop.pk,
            tauM,
            wsz: RefCell::new(bpiop.z.replace(Vec::default())),
            bfold: &bpiop.bfold,
            bscvd, bsccd
        }
    }
}

impl<'a, F, const LOG: bool> BlindSumcheck<2, LOG> for BlindvMMLincheck<'a, F, LOG>
    where F: RingStore<Type: Field + FiniteRing> + Clone,
          <SlotRing as RingStore>::Type: CanIsoFromTo<<F as RingStore>::Type>
{
    type SCB = vMMLincheckBase<'a, DPCS<'a, F>>;

    fn getN() -> usize {
        1
    }
    
    fn avoid_automorphisms() -> bool {
        //TODO: set to true?
        false
    }

    fn get_verifier_data(&self) -> Option<&BlindSumcheckVerifierData<'_>> {
        (&self.bscvd).as_ref()
    }

    fn get_compress_data(&self) -> &BlindSumcheckCompressData<'_, LOG> {
        &self.bsccd
    }
    
    fn logpack(&self) -> usize {
        self.logpack
    }

    fn get_gbfv(&self) -> &GBFV<LOG> {
        &self.bfold.get_gbfv()
    }

    fn get_pk(&self) -> &PublicKey {
        self.pk
    }

    fn get_base(&self) -> &Self::SCB {
        self.plain.get_base()
    }

    fn compute_term_pt(ring: &F, atct: Vec<&El<F>>, atpt: Option<&El<F>>, scalar: &El<F>) -> El<F>
    {
        vMMLincheck::<DPCS<F>>::compute_term(ring, [atct[0], atpt.unwrap()], scalar)
    }

    fn get_workspace_ct(&self) -> Vec<&RefCell<Vec<Ct>>> {
        vec![&self.wsz]
    }

    fn get_reference_pt(&self) -> Option<&[El<F>]> {
        Some(&self.plain.get_reference()[0])
    }

    fn get_workspace_pt(&self) -> Option<&RefCell<Vec<El<F>>>> {
        Some(&self.plain.get_workspace()[0])
    }

    fn get_workspace_pt_ctring(&self) -> Option<&RefCell<Vec<El<CiphertextRing>>>> {
        (&self.tauM).as_ref()
    }

    #[instrument(skip_all)]
    fn compute_term<I, J>(gbfv: &GBFV<LOG>, _pk: &PublicKey,
        atct: Vec<&Ct>, atpt: I, atpt_ctring: Option<&El<CiphertextRing>>, _scalars: J) -> Ct
        where I: Iterator<Item = Option<El<SlotRing>>>, J: Iterator<Item = El<SlotRing>>
    {
        if let Some(pt_ctring) = atpt_ctring {
            println!("Using ct_ring elements.");
            gbfv.hom_mul_plain_single_small_ref(&atct[0], pt_ctring)
        } else {
            let atptu = atpt.into_iter().map(|el| el.unwrap());
            gbfv.hom_mul_plain_single(&atct[0], atptu)
        }
    }

    #[instrument(skip_all)]
    fn check_eval(self, evals: Option<Vec<Vec<El<F>>>>, rX: Vec<El<F>>, _sk: Option<&SecretKey>)
        -> bool
    {
        let ring = self.get_base().field();
        let piop = self.get_base().get_piop();

        // assert!(VERIFY == evals.is_some()); // TODO

        let wsptopt = self.get_workspace_pt().unwrap();
        let MtaurX = ring.clone_el(&wsptopt.borrow()[0]);
        let taurX = rX.iter().chain(piop.tau().iter()).map(|el| ring.clone_el(el)).collect_vec();
        let (Mcom, Mcoeff) = piop.Mcom_coeff();
        let taurXclone = taurX.iter().map(|el| ring.clone_el(el)).collect_vec();
        let proof = piop.pcs().eval(Mcom, taurXclone, ring.clone_el(&MtaurX),
            Some(Mcoeff), Some(piop.matrix().data()));

        if let Some(o) = evals {
            let y = ring.clone_el(&o[0][0]);
            let z = piop.get_z();
            let ev = evaluate_at_fromevals(ring, piop.varcount_cols(), &rX, z).pop().unwrap();

            ring.eq_el(&y, &ev) && piop.pcs().verify(Mcom, &taurX, MtaurX, &Mcoeff, proof)
        } else { true }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::SystemTime;
    use proofs::commit::basefold::BaseFoldPCS;
    use easygbfv::{tests::{gen_random, test_rot}, params::get_gbfv_128bit};

    const VERIFY: bool = false;

    // from basefold code for 2^127 - 1
    const K0: usize = 4;
    const C: usize = 4;
    const VREP: usize = 1000;

    #[test]
    fn test_multdepth() {

        // let gbfv = get_gbfv_128bit(1, 12, 110, Some(1));
        // let gbfv = get_gbfv_128bit(2, 12, 135, Some(1));
        let gbfv = get_gbfv_128bit(0, 13, 220, Some(1));

        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);

        let mut slots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
        let mut ct = gbfv.enc_slots_single_ref(slots.iter(), &sk);
        
        let mut L = 0;

        while L == 0 || gbfv.dec_slots_single(gbfv.clone_ct(&ct), &sk).zip(slots.iter()).all(|(l, r)|
            gbfv.slot_ring().eq_el(&l, r))
        {
            let tmpct = gbfv.clone_ct(&ct);
            ct = gbfv.hom_mul(ct, tmpct, &pk);

            slots = slots.iter().map(|el| gbfv.slot_ring().mul_ref(el, el)).collect();

            L += 1;
        }

        L -= 1;

        println!("L: {}", L)
    }

    #[test]
    fn test_blindvMM_1() {
        // use tracing_subscriber::prelude::*;
        // let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
        // tracing_subscriber::registry().with(chrome_layer).init();

        // Select HE parameters
        // let gbfv = get_gbfv_128bit(0, 12, 90, Some(1));
        // let gbfv = get_gbfv_128bit(1, 12, 110, Some(1));
        let gbfv = get_gbfv_128bit(2, 12, 135, Some(1));
        // let gbfv = get_gbfv_128bit(0, 13, 220, Some(1));

        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);
        let slotfield = gbfv.slot_field();

        // Initiate random matrix
        let Nrows = 11;
        let Ncols = Nrows;
        let vmm = vMMPIOP::random(&slotfield, Ncols, Nrows, K0, C, VREP);

        // Generate random query
        let z = vmm.get_z();
        let hom = gbfv.slot_ring().can_hom(&slotfield).unwrap();
        let z = gbfv.enc_slots_map_ref(z.iter(), &hom, &sk);

        // Compute PCMV
        let zM = gbfv.hom_matmul(vmm.matrix(), &z, &pk);
        println!("Noise budget after PCMV: {}", gbfv.noise_budget(&zM, &sk));
        let response_size = (gbfv.ct_size()*(zM.len() as u64)) as f64
            / (8f64*10f64.powi(3));
        println!("Output size (before MS): {} kB", response_size);
        let outputslots = VERIFY.then(|| {
            let tmp = gbfv.dec_slots(gbfv.clone_cts(zM.iter()), &sk).collect_vec();
            test_rot(&gbfv.slot_ring(), &tmp,
                &vmm.matrix().mul(vmm.get_z()).into_iter().map(|el| hom.map(el)).collect(), 0);
            tmp
        });

        // Test modswitching down PCMV result
        // let (gbfv_ms, old_ctring) = gbfv.mod_switch(30);
        let (gbfv_ms, old_ctring) = gbfv.mod_switch(50);
        let sk_ms = gbfv_ms.mod_switch_sk(&sk, &old_ctring);

        let now = SystemTime::now();
        let zM_ms = gbfv_ms.mod_switch_ct_ref(&zM, &old_ctring);
        println!("TEST: MS time: {}s", now.elapsed().unwrap().as_secs_f32());

        if let Some(outputslots) = outputslots {
            let tmp = gbfv_ms.dec_slots(gbfv_ms.clone_cts(zM_ms.iter()), &sk_ms).collect_vec();
            test_rot(&gbfv_ms.slot_ring(), &outputslots, &tmp, 0);
        }
        println!("Noise budget after MS: {}", gbfv_ms.noise_budget(&zM_ms, &sk_ms));
        let response_size = (gbfv_ms.ct_size()*(zM.len() as u64)) as f64
            / (8f64*10f64.powi(3));
        println!("Output size (after MS): {} kB", response_size);

    }


    #[test]
    fn test_blindvMM_2() {
        // use tracing_subscriber::prelude::*;
        // let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
        // tracing_subscriber::registry().with(chrome_layer).init();

        const PRE_ENCODE: bool = false;

        // Select HE parameters
        let gbfv = get_gbfv_128bit(0, 13, 220, Some(1));
        
        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);
        let slotfield = gbfv.slot_field();

        // Initiate random matrix
        let Nrows = 9;
        let Ncols = Nrows;
        let vmm = vMMPIOP::random(&slotfield, Ncols, Nrows, K0, C, VREP);

        // Generate random query
        let z = vmm.get_z();
        let hom = gbfv.slot_ring().can_hom(&slotfield).unwrap();
        let z = gbfv.enc_slots_map_ref(z.iter(), &hom, &sk);

        // Initialize the vCOEDMV I prover
        let bf = BaseFoldPCS::new(&slotfield, Ncols, gbfv.pack(), 2, Some(VREP)); // dummy
        let bvmm = BlindvMMPIOP::from_plain(vmm, &bf, &gbfv, &pk, z);

        let gbfv = get_gbfv_128bit(0, 13, 220, Some(1)); // TODO: implement clone for GBFV
        let (gbfv_ms, old_ctring) = gbfv.mod_switch(30);
        let sk_ms = gbfv_ms.mod_switch_sk(&sk, &old_ctring);
        let bscmsd = Some(BlindSumcheckMSData {
            gbfv_ms: &gbfv_ms, old_ctring: &old_ctring, sk_ms: VERIFY.then(|| &sk_ms) });

        let response_size = bvmm.proofsize(Some(&gbfv_ms)) as f64 / (8f64*10f64.powi(3));
        println!("Proof size: {} kB", response_size);
        
        // Compute the vCOEDMV I proof
        let now = SystemTime::now();
        assert!(bvmm.execute(PRE_ENCODE, bscmsd, VERIFY.then(|| &sk)));
        let secs = now.elapsed().unwrap().as_secs_f64();
        println!("TEST: Prover time: {:.2}s", secs);
        println!("TEST: Prover throughput: {:.3} MB/s",
            (bvmm.plain.matrix().size() as f64)/(secs*8f64*(10f64.powi(6))));
    }

    // #[test]
    // fn test_ringswitching_noise() {
    //     // use crate::util::get_gbfv;
    //     // let gbfv = get_gbfv(220, Some(1));
    //     let gbfv = get_gbfv_test(0, 13, 220, Some(1));
    //     let ring = gbfv.slot_ring();
    //     let sk = gbfv.gen_sk();
    //     let pk = gbfv.gen_pk(&sk);

    //     let mut slots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
    //     let mut ct = gbfv.enc_slots_ref(slots.iter(), &sk).pop().unwrap();

    //     for _ in 0..11 {
    //         let scalarslots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
    //         ct = gbfv.hom_mul_plain_single_ref(&ct, scalarslots.iter());
    //         slots = scalarslots.into_iter().zip(slots.iter()).map(|(l, r)|
    //             ring.mul_ref_snd(l, r)).collect();
    //     }
    //     let ct2 = gbfv.clone_ct(&ct);
    //     let ct3 = gbfv.clone_ct(&ct);
    //     ct = gbfv.hom_mul(ct, ct2, &pk);
    //     ct = gbfv.hom_mul(ct, ct3, &pk);
    //     println!("Target noise budget: {}", gbfv.noise_budget_iter(
    //         std::iter::once(&ct), &sk));
    //     slots = slots.into_iter().map(|el| ring.pow(el, 3)).collect();

    //     // let gbfv_ms = get_gbfv(120, Some(1));
    //     let gbfv_ms = get_gbfv_test(0, 13, 30, Some(1));
    //     let sk_ms = gbfv.mod_switch_sk(&sk, &gbfv_ms);
    //     let pk_ms = gbfv_ms.gen_pk(&sk_ms);

    //     ct = gbfv.mod_switch(&[ct], &gbfv_ms).pop().unwrap();
    //     println!("After MS noise budget: {}", gbfv_ms.noise_budget_iter(
    //         std::iter::once(&ct), &sk_ms));

    //     let scalarslots = gen_random(&gbfv_ms.slot_ring(), gbfv_ms.pack(), None);
    //     ct = gbfv_ms.hom_mul_plain_single_ref(&ct, scalarslots.iter());
    //     slots = scalarslots.into_iter().zip(slots.iter()).map(|(l, r)|
    //         ring.mul_ref_snd(l, r)).collect();
    //     ct = gbfv_ms.hom_rotate(ct, 1, &pk_ms);
    //     println!("After RS noise budget: {}", gbfv_ms.noise_budget_iter(
    //         std::iter::once(&ct), &sk_ms));

    //     let slotsout = gbfv_ms.dec_slots_single(ct, &sk_ms).collect_vec();
    //     test_rot(&gbfv.slot_ring(), &slots, &slotsout, 1);
    // }
}

