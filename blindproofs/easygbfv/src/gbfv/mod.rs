use itertools::Itertools;
use rand::{Rng, CryptoRng};
use std::ops::Range;
use std::time::Instant;
use tracing::instrument;

use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::seq::{VectorView, VectorFn};
use feanor_math::homomorphism::{Homomorphism, CanHomFrom, CanHom};
use feanor_math::group::AbelianGroupStore;
use feanor_math::rings::{
    poly::{ PolyRingStore, dense_poly::DensePolyRing },
    zn::{ZnRingStore, ZnRing, zn_big::Zn},
    field::{AsField, AsFieldBase},
    extension::FreeAlgebraStore
};
use feanor_math::serialization::SerializableElementRing;

use fheanor::number_ring::{
    NumberRingQuotientStore,
    NumberRingQuotient,
    AbstractNumberRing,
    galois::{GaloisGroupEl, CyclotomicGaloisGroupOps},
    hypercube::{
        structure::HypercubeStructure,
        isomorphism::{HypercubeIsomorphism, SlotRingOf, BaseRing}
    },
    pow2_cyclotomic::Pow2CyclotomicNumberRing
};
use fheanor::bfv::{
    Pow2HighPrecBFV,
    PlaintextRing as PlaintextRingBFV
};
use fheanor::clpx::{
    Pow2CLPX,
    CLPXInstantiation,
    SecretKey as CLPXSecretKey, SecretKeyDistribution,
    RelinKey as CLPXRelinKey,
    KeySwitchKey as CLPXKeySwitchKey,
    encoding::CLPXPlaintextRing
};
use fheanor::gadget_product::digits::RNSGadgetVectorDigitIndices;
use fheanor::circuit::{
    PlaintextCircuit, create_circuit_cached, Coefficient
};
use fheanor::cache::CachedDataKey;
use fheanor::bfv::BFVInstantiation;

use proofs::util::{ZZbig, matmul::MatrixMul};

use crate::hommatmul::HomMatrixMul;
use crate::gbfv::util::{GBFVEvaluator, compress_circuit};


pub mod util;


type Elb<Rb> = <Rb as RingBase>::Element;
pub type PlaintextRing = CLPXPlaintextRing<Pow2CyclotomicNumberRing, Zn<BigIntRing>>;
pub type PlaintextRingBase = <PlaintextRing as RingStore>::Type;
pub type SlotRing = SlotRingOf<PlaintextRing>;
pub type SlotField = AsField<SlotRing>;
pub type CiphertextRingBase = <Pow2CLPX as CLPXInstantiation>::CiphertextRing;
pub type CiphertextRing = RingValue<CiphertextRingBase>;
pub type Ciphertext = (El<CiphertextRing>, El<CiphertextRing>);
pub type SecretKey = CLPXSecretKey<Pow2CLPX>;
pub type RelinKey = CLPXRelinKey<Pow2CLPX>;
pub type KeySwitchKey = CLPXKeySwitchKey<Pow2CLPX>;
pub type GaloisKey = (GaloisGroupEl, KeySwitchKey);
pub type CTCircuit = PlaintextCircuit<CiphertextRingBase>;
pub type PTCircuit = PlaintextCircuit<PlaintextRingBase>;

pub struct GBFV_PtParams {
    pub log2_N: usize,
    pub k: usize,
    pub p: El<BigIntRing>,
    pub t: El<DensePolyRing<BigIntRing>>,
    pub pack_factor: usize,
    pub log2_t_can_bound: usize,
    pub log2_q: Range<usize>
}

pub struct PublicKey {
    rk: RelinKey,
    gks: Vec<GaloisKey>,
}

pub struct GBFV<const LOG: bool = true> {
    cache_dir: String, 
    hciso: HypercubeIsomorphism<PlaintextRing>,
    ctring: CiphertextRing,
    ctringmult: CiphertextRing,
    pack: usize,
    log2_t_can_bound: usize
}

impl<const LOG: bool> GBFV<LOG> {

    #[instrument(skip_all)]
    pub fn new(ptparams: GBFV_PtParams, cache_dir: Option<&str>) -> Self
    {
        let clpxparams = Pow2CLPX::new(2 << ptparams.log2_N);
        let nr = CLPXInstantiation::number_ring(&clpxparams);
        let gg = nr.galois_group();

        // use feanor_math::rings::zn::ZnRing;
        // let Zm = gg.underlying_ring();
        // let Zmgen = Zm.int_hom().map(5);
        // let ZmIntring = Zm.get_ring().integer_ring();
        // let Zmk = Zn::new(ZmIntring, ZmIntring.int_hom().map(
        //         ((1 << (ptparams.log2_N + 1))/ ptparams.k) as i32));
        // let mut Zmkgen = Zm.clone_el(&Zmgen);
        // let ZZ_to_Zmk = Zmk.int_hom();
        // while !Zmk.is_one(&ZZ_to_Zmk.map(Zm.get_ring().any_lift(Zm.clone_el(&Zmkgen)) as i32)) {
        //     Zm.mul_assign_ref(&mut Zmkgen, &Zmgen);
        // }
        // let acting_gg = gg.get_group().clone().subgroup([
        //     gg.from_representative(Zm.get_ring().any_lift(Zmkgen))]);
        let acting_gg = gg.get_group().clone().subgroup([
            gg.pow(&gg.from_representative(5), 
                &ZZbig.int_hom().map((1 << ptparams.log2_N)/(2*ptparams.k) as i32))
        ]);

        let ZZX = DensePolyRing::new(ZZbig, "X");
        let tclone = ZZX.clone_el(&ptparams.t);
        let ptring = CLPXInstantiation::create_plaintext_ring::<LOG>(&clpxparams, ZZX,
            tclone, ZZbig.clone_el(&ptparams.p), acting_gg);
        let hc = HypercubeStructure::default_pow2_hypercube(ptring.acting_galois_group(), ptparams.p);
        let cache_dir = if let Some(dir) = cache_dir { Some(dir) } else { Some("./data/cache") };
        let hciso = HypercubeIsomorphism::new::<LOG>(ptring, &hc, cache_dir);

        assert!(hciso.slot_count() % ptparams.pack_factor == 0);
        let pack = hciso.slot_count() / ptparams.pack_factor;

        let (ctring, ctringmult) = CLPXInstantiation::create_ciphertext_rings(&clpxparams,
            ptparams.log2_q, ptparams.log2_t_can_bound);

        Self {
            cache_dir: cache_dir.unwrap().to_string(),
            hciso,
            ctring,
            ctringmult,
            pack,
            log2_t_can_bound: ptparams.log2_t_can_bound
        }
    }

    pub fn cache_dir(&self) -> &str {
        &self.cache_dir
    }

    pub fn pack(&self) -> usize {
        self.pack
    }

    pub fn ciphertext_ring(&self) -> &CiphertextRing {
        &self.ctring
    }

    pub fn plaintext_ring(&self) -> &PlaintextRing {
        self.hciso.ring()
    }

    pub fn plaintext_modulus(&self) -> El<BigIntRing> {
        self.plaintext_ring().get_ring().characteristic(ZZbig).unwrap()
    }

    fn plaintext_ring_bfv(&self) -> PlaintextRingBFV<Pow2HighPrecBFV> {
        Pow2HighPrecBFV::new(self.plaintext_ring().number_ring().m() as usize)
            .create_plaintext_ring(self.plaintext_modulus())
    }

    pub fn native_pack_factor(&self) -> usize {
        self.hciso.slot_count()/self.pack()
    }

    pub fn slot_ring(&self) -> &SlotRing {
        self.hciso.slot_ring()
    }

    pub fn slot_field(&self) -> SlotField {
        RingValue::from(AsFieldBase::promise_is_perfect_field(self.slot_ring().clone()))
    }

    pub fn hciso(&self) -> &HypercubeIsomorphism<PlaintextRing> {
        &self.hciso
    }

    pub fn id(&self) -> (u64, El<BigIntRing>, usize, usize) {
        (
            self.plaintext_ring().number_ring().m(),
            self.plaintext_modulus(),
            self.pack(),
            self.native_pack_factor()
        )
    }

    pub fn id_string(&self) -> String {
        let (m, p, pack, npf) = self.id();
        format!("m{}_p{}_pack{}_npf{}", m.ilog2(), ZZbig.abs_log2_ceil(&p).unwrap(), pack, npf)
    }

    #[instrument(skip_all)]
    pub fn gen_sk(&self) -> SecretKey {
        let mut rng = rand::rng();
        <Pow2CLPX as CLPXInstantiation>::gen_sk(&self.ctring, &mut rng,
            SecretKeyDistribution::SparseWithHwt(128))
    }

    #[instrument(skip_all)]
    fn gen_rk(&self, sk: &SecretKey, digits: usize) -> RelinKey
    {
        let rng = rand::rng();
        <Pow2CLPX as CLPXInstantiation>::gen_rk(&self.ctring, rng, sk,
            &RNSGadgetVectorDigitIndices::select_digits(digits, self.ctring.base_ring().len()), 3.2)
    }

    #[instrument(skip_all)]
    fn gen_switch_key<R: Rng + CryptoRng>(&self, rng: R, old_sk: &SecretKey, new_sk: &SecretKey,
        digits: usize) -> KeySwitchKey
    {
        <Pow2CLPX as CLPXInstantiation>::gen_switch_key(&self.ctring, rng, old_sk, new_sk,
            &RNSGadgetVectorDigitIndices::select_digits(digits, self.ctring.base_ring().len()), 3.2)
    }

    #[instrument(skip_all)]
    fn all_galois_keys(&self, sk: &SecretKey, digits: usize) -> Vec<GaloisKey>
    {
        let m = self.native_pack_factor();
        let gg = self.hciso().galois_group();
        (0..self.pack()).map(|by| {
            let gs = self.get_rot_galois_el(by*m);
            (gg.clone_el(&gs), self.gen_switch_key(rand::rng(),
                &self.ctring.get_ring().apply_galois_action(sk, &gs),
            sk, digits))}).collect()
    }

    pub fn gen_pk(&self, sk: &SecretKey) -> PublicKey {
        let digits = self.ctring.get_ring().unmanaged_ring()
            .get_ring().ring_decompositions().len();
        PublicKey {
            rk: self.gen_rk(sk, digits),
            gks: self.all_galois_keys(sk, digits)
        }
    }


    pub fn key_switch(&self, ct: Ciphertext, ksk: &KeySwitchKey) -> Ciphertext {
        <Pow2CLPX as CLPXInstantiation>::key_switch(self.ciphertext_ring(), ct, ksk)
    }

    
    pub fn mod_switch(self, log2_q: usize) -> (Self, CiphertextRing) {
        
        let clpxparams = Pow2CLPX::new(self.plaintext_ring().number_ring().m() as usize);
        let (ctring, ctringmult) = CLPXInstantiation::create_ciphertext_rings(&clpxparams,
            log2_q+5..log2_q+10, self.log2_t_can_bound);

        (Self {
            cache_dir: self.cache_dir,
            hciso: self.hciso,
            ctring,
            ctringmult,
            pack: self.pack,
            log2_t_can_bound: self.log2_t_can_bound
        }, self.ctring)
    }

    #[instrument(skip_all)]
    pub fn mod_switch_ct_ref(&self, cts: &[Ciphertext], from_ctring: &CiphertextRing)
        -> Vec<Ciphertext>
    {
        cts.iter().map(|ct| self.mod_switch_ct(self.clone_ct(ct), from_ctring)).collect()
    }

    // modswitches into the GBFV instance denoted by self
    #[instrument(skip_all)]
    pub fn mod_switch_ct(&self, ct: Ciphertext, from_ctring: &CiphertextRing) -> Ciphertext
    {
        <Pow2HighPrecBFV as BFVInstantiation>::mod_switch_ct(&self.plaintext_ring_bfv(),
            self.ciphertext_ring(), from_ctring, ct)
    }

    // modswitches into the GBFV instance denoted by self
    #[instrument(skip_all)]
    pub fn mod_switch_sk(&self, sk: &SecretKey, from_ctring: &CiphertextRing) -> SecretKey
    {
        <Pow2HighPrecBFV as BFVInstantiation>::mod_switch_sk(&self.plaintext_ring_bfv(),
            self.ciphertext_ring(), from_ctring, sk)
    }


    #[instrument(skip_all)]
    pub fn encode_slots_single<I>(&self, ptslots: I) -> El<PlaintextRing>
        where I: Iterator<Item = El<SlotRing>>
    {
        let m = self.hciso.slot_count() / self.pack();
        self.hciso.from_slot_values(
            ptslots.flat_map(|a| (0..m).map(move |_| self.slot_ring().clone_el(&a)))
        )
    }

    #[instrument(skip_all)]
    pub fn encode_slots_single_ref<'a, I>(&self, ptslots: I) -> El<PlaintextRing>
        where I: Iterator<Item = &'a El<SlotRing>>
    {
        self.encode_slots_single(ptslots.map(|el| self.slot_ring().clone_el(el)))
    }

    #[instrument(skip_all)]
    pub fn enc_slots_single<I>(&self, ptslots: I, sk: &SecretKey) -> Ciphertext
        where I: Itertools<Item = El<SlotRing>>
    {
        //assert!(ptslots.count() == self.pack());
        let mut rng = rand::rng();
        <Pow2CLPX as CLPXInstantiation>::enc_sym(&self.plaintext_ring(), &self.ctring, &mut rng,
            &self.encode_slots_single(ptslots), sk, 3.2)
    }

    #[instrument(skip_all)]
    pub fn enc_slots_single_ref<'a, I>(&self, ptslots: I, sk: &SecretKey) -> Ciphertext
        where I: Itertools<Item = &'a El<SlotRing>>
    {
        //assert!(ptslots.count() == self.pack());
        self.enc_slots_single(ptslots.map(|el| self.slot_ring().clone_el(el)), sk)
    }

    #[instrument(skip_all)]
    pub fn enc_slots<I>(&self, ptslots: I, sk: &SecretKey) -> Vec<Ciphertext>
        where I: Itertools<Item = El<SlotRing>>
    {
        //assert!(ptslots.count() % self.pack() == 0);
        ptslots.chunks(self.pack()).into_iter().map(|chunk_of_slots|
            self.enc_slots_single(chunk_of_slots, sk)).collect()
    }

    #[instrument(skip_all)]
    pub fn enc_slots_ref<'a, I>(&self, ptslots: I, sk: &SecretKey) -> Vec<Ciphertext>
        where I: Itertools<Item = &'a El<SlotRing>>
    {
        //assert!(ptslots.count() % m == 0);
        self.enc_slots(ptslots.map(|el| self.slot_ring().clone_el(el)), sk)
    }

    #[instrument(skip_all)]
    pub fn enc_slots_map<'a, I, R>(&self, ptslots: I,
        hom: &CanHom<&'a R, &'a SlotRing>, sk: &SecretKey) -> Vec<Ciphertext>
        where I: Itertools<Item = El<R>>, R: RingStore,
              <SlotRing as RingStore>::Type: CanHomFrom<<R as RingStore>::Type>
    {
        self.enc_slots(ptslots.map(|el| hom.map(el)), &sk)
    }

    #[instrument(skip_all)]
    pub fn enc_slots_map_ref<'a, 'b, I, R>(&self, ptslots: I,
        hom: &CanHom<&'a R, &'a SlotRing>, sk: &SecretKey) -> Vec<Ciphertext>
        where I: Itertools<Item = &'b El<R>>, R: RingStore,
              <SlotRing as RingStore>::Type: CanHomFrom<<R as RingStore>::Type>, 'a: 'b
    {
        self.enc_slots(ptslots.map(|el| hom.map_ref(el)), &sk)
    }

    #[instrument(skip_all)]
    pub fn enc_firstslot(&self, ptslot: El<SlotRing>) -> impl Itertools<Item = El<SlotRing>> {
        std::iter::once(ptslot).chain(
            std::iter::repeat_with(|| self.slot_ring().zero()).take(self.pack() - 1))
    }

    #[instrument(skip_all)]
    pub fn enc_firstslot_map_ref<'a, R>(&self, ptslot: &El<R>,
        hom: &CanHom<&'a R, &'a SlotRing>, sk: &SecretKey) -> Ciphertext
        where R: RingStore, <SlotRing as RingStore>::Type: CanHomFrom<<R as RingStore>::Type>
    {
        self.enc_slots_single(self.enc_firstslot(hom.map_ref(ptslot)), &sk)
    }


    #[instrument(skip_all)]
    pub fn decode_slots_single(&self, pt: El<PlaintextRing>) -> impl Iterator<Item = El<SlotRing>>
    {
        self.hciso.hypercube().element_iter().step_by(self.native_pack_factor()).map(move |g|
            self.hciso.get_slot_value(&pt, &g))
    }

    #[instrument(skip_all)]
    pub fn dec_slots_single(&self, ct: Ciphertext, sk: &SecretKey)
        -> impl Iterator<Item = El<SlotRing>>
    {
        self.decode_slots_single(
            <Pow2CLPX as CLPXInstantiation>::dec(&self.plaintext_ring(), &self.ctring, ct, sk))
    }

    #[instrument(skip_all)]
    pub fn dec_slots_single_map<'a, Rb, H>(&self, ct: Ciphertext, sk: &SecretKey, hom: &H)
        -> impl Iterator<Item = Elb<Rb>>
        where Rb: RingBase + ?Sized, H: Homomorphism<<SlotRing as RingStore>::Type, Rb>
    {
        self.dec_slots_single(ct, sk).map(|el| hom.map(el))
    }

    #[instrument(skip_all)]
    pub fn dec_slots_single_sum(&self, ct: Ciphertext, sk: &SecretKey) -> El<SlotRing> {
        self.dec_slots_single(ct, sk).fold(self.slot_ring().zero(), |acc, x|
            self.slot_ring().add(acc, x))
    }

    #[instrument(skip_all)]
    pub fn dec_slots(&self, cts: Vec<Ciphertext>, sk: &SecretKey)
        -> impl Iterator<Item = El<SlotRing>>
    {
        cts.into_iter().flat_map(|ct| self.dec_slots_single(ct, sk))
    }

    // TODO: change this to CanHom
    #[instrument(skip_all)]
    pub fn dec_slots_map<'a, Rb, H>(&self, cts: Vec<Ciphertext>, sk: &SecretKey, hom: &H)
        -> impl Iterator<Item = Elb<Rb>>
        where Rb: RingBase + ?Sized, H: Homomorphism<<SlotRing as RingStore>::Type, Rb>
    {
        self.dec_slots(cts, sk).map(|el| hom.map(el))
    }

    pub fn println_slots(&self, ct: &Ciphertext, sk: &SecretKey) {
        self.dec_slots_single(self.clone_ct(ct), sk).for_each(|sl|
            self.slot_ring().println(&sl)
        )
    }

    pub fn println_slots_sum(&self, ct: &Ciphertext, sk: &SecretKey) {
        self.slot_ring().println(&self.dec_slots_single_sum(self.clone_ct(ct), sk))
    }

    pub fn make_coefficient(&self, slots: Vec<El<SlotRing>>) -> Coefficient<PlaintextRingBase>
    {
        let slotring = self.slot_ring();
        if slots.iter().all(|el| slotring.is_zero(el)) {
            Coefficient::Zero
        } else if slots.iter().all(|el| slotring.is_one(el)) {
            Coefficient::One
        } else {
            Coefficient::Other(self.encode_slots_single(slots.into_iter()))
        }
    }
    
    #[instrument(skip_all)]
    pub fn clone_ct(&self, input: &Ciphertext) -> Ciphertext
    {
        <Pow2CLPX as CLPXInstantiation>::clone_ct(&self.ctring, input)
    }

    pub fn clone_cts<'a, I>(&self, input: I) -> Vec<Ciphertext>
        where I: Iterator<Item = &'a Ciphertext>
    {
        input.map(|ct| self.clone_ct(ct)).collect()
    }

    pub fn ct_zero(&self) -> Ciphertext {
        <Pow2CLPX as CLPXInstantiation>::transparent_zero(&self.ctring)
    }

    pub fn negate(&self, ct: Ciphertext) -> Ciphertext {
        (self.ctring.negate(ct.0), self.ctring.negate(ct.1))
    }


    //// TODO: add all variants
    #[instrument(skip_all)]
    pub fn hom_add_single(&self, lct: Ciphertext, rct: Ciphertext) -> Ciphertext
    {
        (self.ctring.add(lct.0, rct.0), self.ctring.add(lct.1, rct.1))
    }

    #[instrument(skip_all)]
    pub fn hom_add_single_ref(&self, lct: &Ciphertext, rct: &Ciphertext) -> Ciphertext
    {
        self.hom_add_single(self.clone_ct(lct), self.clone_ct(rct))
    }

    //// TODO: check whether this is faster than owning inputs and allocating new memory
    #[instrument(skip_all)]
    pub fn hom_add_assign_single(&self, lct: &mut Ciphertext, rct: &Ciphertext)
    {
        self.ctring.add_assign_ref(&mut lct.0, &rct.0);
        self.ctring.add_assign_ref(&mut lct.1, &rct.1);
    }

    #[instrument(skip_all)]
    pub fn hom_add_assign<'a, I, J>(&self, lcts: I, rcts: J)
        where I: Iterator<Item = &'a mut Ciphertext>, J: Iterator<Item = &'a Ciphertext>
    {
        lcts.zip(rcts).for_each(|(lct, rct)| self.hom_add_assign_single(lct, rct));
    }

    #[instrument(skip_all)]
    pub fn hom_add_assign_to_single(&self, oct: &mut Ciphertext, lct: &Ciphertext, rct: &Ciphertext)
    {
        oct.0 = self.ctring.add_ref(&lct.0, &rct.0);
        oct.1 = self.ctring.add_ref(&lct.1, &rct.1);
    }

    #[instrument(skip_all)]
    pub fn hom_add_assign_to<'a, I, J>(&self, octs: I, lcts: J, rcts: J)
        where I: Iterator<Item = &'a mut Ciphertext>, J: Iterator<Item = &'a Ciphertext>
    {
        octs.zip(lcts.zip(rcts)).for_each(|(oct, (lct, rct))|
            self.hom_add_assign_to_single(oct, lct, rct));
    }

    #[instrument(skip_all)]
    pub fn hom_add_plain_single<I>(&self, ct: Ciphertext, ptslots: I) -> Ciphertext
        where I: Iterator<Item = El<SlotRing>>
    {
        <Pow2CLPX as CLPXInstantiation>::hom_add_plain(self.plaintext_ring(),
            self.ciphertext_ring(), &self.encode_slots_single(ptslots), ct)
    }

    #[instrument(skip_all)]
    pub fn hom_sub_single(&self, lct: Ciphertext, rct: Ciphertext) -> Ciphertext
    {
        (self.ctring.sub(lct.0, rct.0), self.ctring.sub(lct.1, rct.1))
    }

    #[instrument(skip_all)]
    pub fn hom_sub_single_ref(&self, lct: &Ciphertext, rct: &Ciphertext) -> Ciphertext
    {
        self.hom_sub_single(self.clone_ct(lct), self.clone_ct(rct))
    }

    #[instrument(skip_all)]
    pub fn hom_sub_assign<'a, I, J>(&self, lcts: I, rcts: J)
        where I: Iterator<Item = &'a mut Ciphertext>, J: Iterator<Item = &'a Ciphertext>
    {
        lcts.zip(rcts).for_each(|(lct, rct)| {
            self.ctring.sub_assign_ref(&mut lct.0, &rct.0);
            self.ctring.sub_assign_ref(&mut lct.1, &rct.1);
        });
    }

    #[instrument(skip_all)]
    pub fn hom_sub_assign_to<'a, I, J>(&self, octs: I, lcts: J, rcts: J)
        where I: Iterator<Item = &'a mut Ciphertext>, J: Iterator<Item = &'a Ciphertext>
    {
        octs.zip(lcts.zip(rcts)).for_each(|(oct, (lct, rct))| {
            oct.0 = self.ctring.sub_ref(&lct.0, &rct.0);
            oct.1 = self.ctring.sub_ref(&lct.1, &rct.1);
        });
    }

    #[instrument(skip_all)]
    pub fn hom_square_single(&self, ct: Ciphertext, pk: &PublicKey) -> Ciphertext {
        <Pow2CLPX as CLPXInstantiation>::hom_square(
            &self.plaintext_ring(), &self.ctring, &self.ctringmult, ct, &pk.rk)
    }

    #[instrument(skip_all)]
    pub fn hom_square(&self, cts: Vec<Ciphertext>, pk: &PublicKey) -> Vec<Ciphertext> {
        cts.into_iter().map(|ct| self.hom_square_single(ct, pk)).collect()
    }


    #[instrument(skip_all)]
    pub fn hom_mul(&self, l: Ciphertext, r: Ciphertext, pk: &PublicKey) -> Ciphertext {
        <Pow2CLPX as CLPXInstantiation>::hom_mul(self.plaintext_ring(), self.ciphertext_ring(),
            &self.ctringmult, l, r, &pk.rk)
    }

    #[instrument(skip_all)]
    pub fn hom_mul_ref(&self, l: &Ciphertext, r: &Ciphertext, pk: &PublicKey) -> Ciphertext {
        self.hom_mul(self.clone_ct(l), self.clone_ct(r), pk)
    }

    //////////////////////// HOM_MUL_PLAIN_SINGLE
    // ptel input is assumed to be small lift
    #[instrument(skip_all)]
    pub fn hom_mul_plain_single_small_ref(&self, ct: &Ciphertext, ptel: &El<CiphertextRing>)
        -> Ciphertext
    {
        let C = self.ciphertext_ring();
        (C.mul_ref(&ct.0, ptel), C.mul_ref(&ct.1, ptel))
    }

    // TODO: make version that does not clone ciphertexts!!!
    #[instrument(skip_all)]
    fn hom_mul_plain_single_ptring(&self, ct: &Ciphertext, ptel: &El<PlaintextRing>)
        -> Ciphertext
    {
        <Pow2CLPX as CLPXInstantiation>::hom_mul_plain(&self.plaintext_ring(), &self.ctring,
            ptel, self.clone_ct(&ct))
    }
    
    #[instrument(skip_all)]
    // make sure that ptslots has self.pack() items
    pub fn hom_mul_plain_single_map<'a, I, Rb, H>(&self, ct: &Ciphertext, ptslots: I, hom: &H)
        -> Ciphertext
        where I: Iterator<Item = Elb<Rb>>, Rb: RingBase + ?Sized,
            H: Homomorphism<Rb, <SlotRing as RingStore>::Type>
    {
        self.hom_mul_plain_single_ptring(ct, &self.encode_slots_single(ptslots.map(|el| hom.map(el))))
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plain_single<I>(&self, ct: &Ciphertext, ptslots: I) -> Ciphertext
        where I: Iterator<Item = El<SlotRing>>
    {
        self.hom_mul_plain_single_map(ct, ptslots, &self.slot_ring().identity())
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plain_single_ref<'a, I>(&self, ct: &Ciphertext, ptslots: I) -> Ciphertext
        where I: Iterator<Item = &'a El<SlotRing>>
    {
        self.hom_mul_plain_single(ct, ptslots.map(|sl| self.slot_ring().clone_el(sl)))
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plain_single_map_ref<'a, 'b, 'c, I, Rb, H>(&'a self, ct: &Ciphertext, ptslots: I,
        hom: &H) -> Ciphertext
        where I: Iterator<Item = &'c Elb<Rb>>, Rb: RingBase + ?Sized, Elb<Rb>: 'c,
            H: Homomorphism<Rb, <SlotRing as RingStore>::Type>
    {
        self.hom_mul_plain_single(ct, ptslots.map(|el| hom.map_ref(el)))
    }


    //////////////////////// HOM_MUL_PLAIN
    #[instrument(skip_all)]
    pub fn hom_mul_plain_map<'a, I, Rb, H>(&self, cts: &[Ciphertext], ptslots: I, hom: &H)
        -> Vec<Ciphertext>
        where I: Itertools<Item = Elb<Rb>>, Rb: RingBase + ?Sized,
            H: Homomorphism<Rb, <SlotRing as RingStore>::Type>
    {
        ptslots.chunks(self.pack()).into_iter().zip(cts.iter()).map(|(slotschunk, ct)|
            self.hom_mul_plain_single_map(ct, slotschunk, hom)).collect()
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plain<I>(&self, cts: &[Ciphertext], ptslots: I) -> Vec<Ciphertext>
        where I: Itertools<Item = El<SlotRing>>
    {
        self.hom_mul_plain_map(cts, ptslots, &self.slot_ring().identity())
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plain_ref<'a, I>(&self, cts: &[Ciphertext], ptslots: I) -> Vec<Ciphertext>
        where I: Itertools<Item = &'a El<SlotRing>>
    {
        self.hom_mul_plain(cts, ptslots.map(|el| self.slot_ring().clone_el(el)))
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plain_map_ref<'a, I, Rb, H>(&'a self, cts: &[Ciphertext], ptslots: I, hom: &H)
        -> Vec<Ciphertext>
        where I: Itertools<Item = &'a Elb<Rb>>, Rb: RingBase + ?Sized, Elb<Rb>: 'a,
            H: Homomorphism<Rb, <SlotRing as RingStore>::Type>
    {
        self.hom_mul_plain(cts, ptslots.map(|el| hom.map_ref(el)))
    }


    ////////////////////// HOM_MUL_PLAINSLOT_SINGLE
    #[instrument(skip_all)]
    pub fn hom_mul_plainslot_single_map<'a, Rb, H>(&self, ct: &Ciphertext, ptslot: Elb<Rb>, hom: &H)
        -> Ciphertext
        where Rb: RingBase + ?Sized, H: Homomorphism<Rb, <SlotRing as RingStore>::Type>
    {
        let mapped = hom.map(ptslot);
        self.hom_mul_plain_single(ct, (0..self.pack()).map(|_| self.slot_ring().clone_el(&mapped)))
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plainslot_single(&self, ct: &Ciphertext, ptslot: El<SlotRing>) -> Ciphertext
    {
        self.hom_mul_plainslot_single_map(ct, ptslot, &self.slot_ring().identity())
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plainslot_single_ref(&self, ct: &Ciphertext, ptslot: &El<SlotRing>) -> Ciphertext
    {
        self.hom_mul_plainslot_single(ct, self.slot_ring().clone_el(ptslot))
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plainslot_single_map_ref<'a, Rb, H>(&self, ct: &Ciphertext, ptslot: &Elb<Rb>,
        hom: &H) -> Ciphertext
        where Rb: RingBase + ?Sized, H: Homomorphism<Rb, <SlotRing as RingStore>::Type>
    {
        self.hom_mul_plainslot_single(ct, hom.map_ref(ptslot))
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plain_add_single_small_ref(&self, toadd: Ciphertext, tomul: &Ciphertext,
        mul: &El<CiphertextRing>) -> Ciphertext
    {
        let mul_add = |a: El<CiphertextRing>, b: &El<CiphertextRing>, mul: &El<CiphertextRing>| {
            self.ciphertext_ring().add(a, self.ciphertext_ring().mul_ref(b, mul))
        };
        (mul_add(toadd.0, &tomul.0, mul), mul_add(toadd.1, &tomul.1, mul))
    }

    #[instrument(skip_all)]
    pub fn hom_mul_plain_add_map_ref<'a, 'b, 'c, I, J, Rb, H>(&'a self, cts: I, ptslots: J, hom: &H)
        -> Ciphertext
        where I: Itertools<Item = &'a Ciphertext>, J: Itertools<Item = &'c Elb<Rb>>,
            Rb: RingBase + ?Sized, H: Homomorphism<Rb, <SlotRing as RingStore>::Type>, Elb<Rb>: 'c
    {
        ptslots.chunks(self.pack()).into_iter().zip(cts).map(|(slotschunk, ct)|
            self.hom_mul_plain_single_map_ref(ct, slotschunk, hom)   
        ).fold(self.ct_zero(), move |acc, ct| self.hom_add_single_ref(&acc, &ct))
    }


    pub fn get_rot_galois_el(&self, by: usize) -> GaloisGroupEl {
        let cgg = self.hciso.galois_group();
        cgg.pow(&cgg.generators()[0], &ZZbig.int_hom().map(by as i32))
    }

    #[instrument(skip_all)]
    pub fn hom_rotate(&self, ct: Ciphertext, by: usize, pk: &PublicKey) -> Ciphertext
    {
        assert!(by > 0);
        let galois_group = self.ctring.acting_galois_group();
        let m = self.native_pack_factor();
        let gby = self.get_rot_galois_el(by*m);
        assert!(pk.gks.len() == self.pack());
        let gk = pk.gks.iter().find(|(g, _)| galois_group.eq_el(g, &gby)).unwrap();
        <Pow2CLPX as CLPXInstantiation>::hom_galois(self.plaintext_ring(),
            &self.ctring, ct, &gby, &gk.1)
    }

    pub fn read_or_create_circuit<F, R>(&self, ring: R, name: &str, create: F)
        -> PlaintextCircuit<R::Type>
        where R: RingStore + Copy,
              R::Type: NumberRingQuotient + SerializableElementRing, BaseRing<R>: ZnRing,
              F: FnOnce() -> PlaintextCircuit<R::Type>
    {
        let key = CachedDataKey::String(format!("{}_{}", name, self.id_string()).to_string());
        create_circuit_cached::<R, _, LOG>(ring, &[key], Some(&self.cache_dir), create)
    }

    // TODO: make this one function
    pub fn evaluate_circuit(&self, circuit: PTCircuit, cts: &[Ciphertext], pk: &PublicKey)
        -> Vec<Ciphertext>
    {
        circuit.evaluate_clpx::<Pow2CLPX, _>(self.plaintext_ring(), self.plaintext_ring(),
            self.ciphertext_ring(), None, cts, None, &pk.gks, None)
    }

    pub fn evaluate_circuit_small(&self, circuit: &CTCircuit, cts: &[Ciphertext],
        pk: &PublicKey) -> Vec<Ciphertext>
    {
        circuit.evaluate_generic::<Ciphertext, GBFVEvaluator<LOG>>(cts,
            GBFVEvaluator::new(&self, pk))
    }

    pub fn lift_to_ctring(&self, ptel: &El<PlaintextRing>) -> El<CiphertextRing> {
        let ptel_poly = self.plaintext_ring().get_ring().small_lift(ptel);
        let C = self.ciphertext_ring();
        let mod_Q = C.base_ring().can_hom(&ZZbig).unwrap();
        C.from_canonical_basis((0..C.rank()).map(|i|
            ZZbig.clone_el(self.plaintext_ring().get_ring().ZZX().coefficient_at(&ptel_poly, i)))
                .map(|c| mod_Q.map(c))
        )
    }

    pub fn lift_circuit(&self, circuit: PTCircuit) -> CTCircuit {
        circuit.change_ring_uniform(|coeff| match coeff {
            Coefficient::Zero => Coefficient::Zero,
            Coefficient::One => Coefficient::One,
            Coefficient::NegOne => Coefficient::NegOne,
            Coefficient::Integer(x) => Coefficient::Integer(x),
            Coefficient::Other(x) => Coefficient::Other(self.lift_to_ctring(&x))
        })
    }

    #[instrument(skip_all)]
    pub fn hom_matmul<R, MM>(&self, matrix: &MM, cts: &[Ciphertext], pk: &PublicKey)
        -> Vec<Ciphertext>
        where R: RingStore, <SlotRing as RingStore>::Type: CanHomFrom<<R as RingStore>::Type>,
              MM: MatrixMul<R = R>
    {
        assert!(matrix.columns() / self.pack() == cts.len());
        let hmm = HomMatrixMul::<R, MM, LOG, true>::new(&matrix, self);
        let name = format!("{}_lifted", matrix.desc());
        let circuit = self.read_or_create_circuit(self.ciphertext_ring(), name.as_str(),
            || self.lift_circuit(hmm.circuit()));
        // let circuit = self.read_or_create_circuit(self.plaintext_ring(), matrix.desc(),
        //     || hmm.circuit());
        let start = Instant::now();
        let res = self.evaluate_circuit_small(&circuit, cts, pk);
        // let res = self.evaluate_circuit(circuit, cts, pk);
        let end = Instant::now();
        let tp = (matrix.size() as f64)/((end-start).as_millis() as f64);
        if LOG {
            println!("Computed hom_matmul with throughput of {:.2} MB/s",
                tp/(8f64*(10f64.powi(3))))
        }
        assert!(matrix.rows() / self.pack() == res.len());
        res
    }

    #[allow(dead_code)]
    fn hom_sumslots_shallow(&self, ct: Ciphertext, pk: &PublicKey) -> Ciphertext
    {
        (1..self.pack()).fold(self.clone_ct(&ct), |acc, i|
            self.hom_add_single(acc, self.hom_rotate(self.clone_ct(&ct), i, pk)))
    }

    #[allow(dead_code)]
    fn hom_sumslots_deep(&self, ct: Ciphertext, pk: &PublicKey) -> Ciphertext
    {
        assert!(self.pack().is_power_of_two());
        let mut res = ct;
        (0..self.pack().ilog2()).for_each(|i| {
            let tmp = self.clone_ct(&res);
            self.hom_add_assign_single(&mut res, &self.hom_rotate(tmp, 1 << i, pk))
        });
        res
    }

    #[allow(dead_code)]
    fn hom_compress_nocircuit<I>(&self, mut cts: I, pk: &PublicKey) -> Ciphertext
        where I: Iterator<Item = Ciphertext>
    {
        let sum_mask = |ct: Ciphertext, i: usize, pk: &PublicKey| {
            let sr = self.slot_ring();
            self.hom_mul_plain_single(&self.hom_sumslots_deep(ct, pk),
                (0..self.pack()).map(|j| if j == i { sr.one() } else { sr.zero() }))
        };
        let ct1 = cts.next().expect("Input length should be greater than one.");
        cts.enumerate().fold(sum_mask(ct1, 0, pk), |acc, (i, ct)|
            self.hom_add_single(acc, sum_mask(ct, i+1, pk)))
    }

    #[instrument(skip_all)]
    pub fn hom_compress<const DEEP: bool>(&self, cts: &[Ciphertext], pk: &PublicKey) -> Ciphertext
    {
        let circuit = self.read_or_create_circuit(self.ciphertext_ring(), "compress_lifted", ||
            self.lift_circuit(compress_circuit::<DEEP, _>(&self, cts.len())));
        let mut res = self.evaluate_circuit_small(&circuit, cts, pk);
        debug_assert!(res.len() == 1);
        res.pop().unwrap()
    }
    

    pub fn noise_budget(&self, cts: &[Ciphertext], sk: &SecretKey) -> usize {
        self.noise_budget_iter(cts.into_iter(), sk)
    }

    pub fn noise_budget_iter<'x, I>(&self, ctiter: I, sk: &SecretKey) -> usize
        where I: Iterator<Item = &'x Ciphertext>
    {
        ctiter.map(|ct| <Pow2CLPX as CLPXInstantiation>::noise_budget(&self.plaintext_ring(), 
            &self.ctring, ct, sk)).min().unwrap()
    }

    // outputs size of one ciphertext in bits
    pub fn ct_size(&self) -> u64 {
        let log2_q = self.ctring.base_ring().integer_ring().abs_log2_ceil(
            self.ctring.base_ring().modulus()).unwrap();
        return 2*(log2_q as u64)*(self.ctring.number_ring().m()/2 as u64)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{test_rot, gen_random, get_gbfv_test};

    #[test]
    fn test_gbfv_encode() {
        let gbfv = get_gbfv_test(0, 8, 100, Some(2));

        let ptslots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
        let pt_gbfv = gbfv.encode_slots_single_ref(ptslots.iter());
        let ptslots2 = gbfv.decode_slots_single(pt_gbfv).collect();

        test_rot(&gbfv.slot_ring(), &ptslots, &ptslots2, 0);
    }

    #[test]
    fn test_gbfv_enc() {
        let gbfv = get_gbfv_test(0, 8, 100, Some(2));
        let sk = gbfv.gen_sk();

        let ptslots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
        let ct = gbfv.enc_slots_single_ref(ptslots.iter(), &sk);
        let ptslots2 = gbfv.dec_slots_single(ct, &sk).collect();

        test_rot(&gbfv.slot_ring(), &ptslots, &ptslots2, 0);
    }

    #[test]
    fn test_gbfv_hom_addsub() {

        let gbfv = get_gbfv_test(0, 8, 100, None);
        let sk = gbfv.gen_sk();

        let N = 3;

        let ptslots1 = gen_random(&gbfv.slot_ring(), gbfv.pack()*N, None);
        let mut cts1 = gbfv.enc_slots_ref(ptslots1.iter(), &sk);
        let ptslots2 = gen_random(&gbfv.slot_ring(), gbfv.pack()*N, None);
        let cts2 = gbfv.enc_slots_ref(ptslots2.iter(), &sk);
        gbfv.hom_add_assign(cts1.iter_mut(), cts2.iter());
        let res = gbfv.dec_slots(cts1, &sk).collect();

        test_rot(&gbfv.slot_ring(), &ptslots1.into_iter().zip(ptslots2).map(
            |(pt1, pt2)| gbfv.slot_ring().add(pt1, pt2)).collect(), &res, 0);
    }

    #[test]
    fn test_gbfv_hom_mul_plain() {

        let gbfv = get_gbfv_test(0, 8, 100, None);
        let sk = gbfv.gen_sk();

        let N = 3;

        let ptslots = gen_random(&gbfv.slot_ring(), gbfv.pack()*N, None);
        let cts = gbfv.enc_slots_ref(ptslots.iter(), &sk);
        let scalarslots = gen_random(&gbfv.slot_ring(), gbfv.pack()*N, None);
        let ct2 = gbfv.hom_mul_plain_ref(&cts, scalarslots.iter());
        let res = gbfv.dec_slots(ct2, &sk).collect();

        test_rot(&gbfv.slot_ring(), &ptslots.into_iter().zip(scalarslots).map(
            |(pt, sc)| gbfv.slot_ring().mul(pt, sc)).collect(), &res, 0);
    }

    #[test]
    fn test_gbfv_hom_square() {

        let gbfv = get_gbfv_test(0, 8, 100, None);
        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);

        let ptslots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
        let ct = gbfv.enc_slots_ref(ptslots.iter(), &sk);
        let ct2 = gbfv.hom_square(ct, &pk);
        let res = gbfv.dec_slots(ct2, &sk).collect();

        test_rot(&gbfv.slot_ring(), &ptslots.into_iter().map(
            |el| gbfv.slot_ring().pow(el, 2)).collect(), &res, 0);
    }

    #[test]
    fn test_gbfv_hom_rot() {

        let gbfv = get_gbfv_test(0, 8, 100, Some(2));
        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);

        let ptslots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
        let ct = gbfv.enc_slots_ref(ptslots.iter(), &sk);

        let rot_by = rand::rng().random_range(1..gbfv.pack());
        let ct2 = ct.into_iter().map(|cti|
            gbfv.hom_rotate(cti, rot_by, &pk)).collect::<Vec<_>>();
        let res = gbfv.dec_slots(ct2, &sk).collect();

        test_rot(&gbfv.slot_ring(), &ptslots, &res, rot_by);
    }

    #[test]
    fn test_gbfv_hom_circuits() {

        let gbfv = get_gbfv_test(0, 8, 100, None);

        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);

        let slotsin = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);

        let ctin = gbfv.enc_slots_ref(slotsin.iter(), &sk);
        let ctout = gbfv.hom_square(ctin, &pk);
        let slotsoutct = gbfv.dec_slots(ctout, &sk).collect();

        let ptin = gbfv.encode_slots_single_ref(slotsin.iter());
        let circuit = PlaintextCircuit::square(gbfv.plaintext_ring());
        let ptout = circuit.evaluate(&[ptin], gbfv.plaintext_ring().identity());
        let slotsoutpt = gbfv.decode_slots_single(
            gbfv.plaintext_ring().clone_el(&ptout[0])).collect();

        test_rot(&gbfv.slot_ring(), &slotsoutpt, &slotsoutct, 0);
    }

    #[test]
    fn test_gbfv_modswitch() {

        let log2_q = 25;
        let log2_q_new = 15;

        let gbfv = get_gbfv_test(0, 8, log2_q, None);
        let sk = gbfv.gen_sk();

        let slotsin = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
        let mut ct = gbfv.enc_slots_ref(slotsin.iter(), &sk).pop().unwrap();
        println!("Fresh noise budget: {}", gbfv.noise_budget_iter(
            std::iter::once(&ct), &sk));
        let scalarslots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
        ct = gbfv.hom_mul_plain_single_ref(&ct, scalarslots.iter());
        println!("After ptct noise budget: {}", gbfv.noise_budget_iter(
            std::iter::once(&ct), &sk));

        let (gbfv_smaller, old_ctring) = gbfv.mod_switch(log2_q_new);
        let sk_smaller = gbfv_smaller.mod_switch_sk(&sk, &old_ctring);

        ct = gbfv_smaller.mod_switch_ct(ct, &old_ctring);
        println!("After modswitch noise budget: {}", gbfv_smaller.noise_budget_iter(
            std::iter::once(&ct), &sk_smaller));
        let slotsout = gbfv_smaller.dec_slots_single(ct, &sk_smaller).collect_vec();

        println!("size: {}", gbfv_smaller.ct_size());

        test_rot(&gbfv_smaller.slot_ring(), &slotsin.into_iter().zip(scalarslots).map(
            |(pt, sc)| gbfv_smaller.slot_ring().mul(pt, sc)).collect(), &slotsout, 0);
    }

    fn test_gbfv_compress<const DEEP: bool>() {
        let gbfv = get_gbfv_test(0, 8, 100, None);
        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);

        let N = 3;

        let ptslots = gen_random(&gbfv.slot_ring(), gbfv.pack()*N, None);
        let cts = gbfv.enc_slots_ref(ptslots.iter(), &sk);
        let ctout = gbfv.hom_compress::<DEEP>(&cts, &pk);

        assert!(gbfv.dec_slots_single(ctout, &sk).zip(cts.into_iter().map(|ct|
            gbfv.dec_slots_single_sum(ct, &sk))).all(|(l, r)|
                gbfv.slot_ring().eq_el(&l, &r)))
    }

    #[test]
    fn test_gbfv_compress_deep() { test_gbfv_compress::<true>() }

    #[test]
    fn test_gbfv_compress_shallow() { test_gbfv_compress::<false>() }

    #[test]
    fn test_gbfv_ringswitching() {

        use crate::params::get_gbfv_16bit;
        use feanor_math::rings::zn::zn_64::Zn;

        let log2_q = 100;
        let mbig = 9;
        let msmall = 8;
        let i = 0;

        let gbfv = get_gbfv_16bit(i, mbig, log2_q, None);
        let sk = gbfv.gen_sk();

        let gbfv_rs = get_gbfv_16bit(i, msmall, log2_q, None);
        let sk_rs = gbfv_rs.gen_sk();

        ////////////////////////////////// Doing the key-switching

        // NOTE: assumes gbfv and gbfv_rs chose the same RNS moduli
        let bigC = gbfv.ciphertext_ring();
        let smallC = gbfv_rs.ciphertext_ring();

        let sk_rs_big = bigC.from_canonical_basis(smallC.wrt_canonical_basis(&sk_rs).into_iter());

        let mut rng = rand::rng();
        let ksk = gbfv.gen_switch_key(&mut rng, &sk, &sk_rs_big,
            bigC.get_ring().unmanaged_ring().get_ring().ring_decompositions().len());

        let ptslots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
        let ct = gbfv.enc_slots_single_ref(ptslots.iter(), &sk);

        let ct_ks = gbfv.key_switch(ct, &ksk);

        let outslots = gbfv.dec_slots_single(ct_ks, &sk_rs_big).collect();
        test_rot(&gbfv.slot_ring(), &ptslots, &outslots, 0); // NOTE: this works

        ////////////////////////////////// Testing automorphisms
        
        // let bigP = gbfv.plaintext_ring();
        // let bigPgg = bigP.acting_galois_group();
        // let smallP = gbfv_rs.plaintext_ring();

        // let ptslots_rs = gen_random(&gbfv.slot_ring(), gbfv_rs.pack(), None);
        // let pt_rs = gbfv_rs.encode_slots_single_ref(ptslots_rs.iter());
        // smallP.println(&pt_rs);
        // println!();

        // let Zmbig = bigPgg.underlying_ring();
        // let Zmsmall = smallP.acting_galois_group().underlying_ring();
        // let ZZ_to_Zmsmall = Zmsmall.int_hom();
        // let gsels = bigPgg.enumerate_elements().filter(|ggel| Zmsmall.is_one(&ZZ_to_Zmsmall.map(
        //     Zmbig.get_ring().any_lift(Zmbig.clone_el(bigPgg.as_ring_el(&ggel))) as i32
        // ))).collect_vec();

        // let pt_rs2 = smallP.apply_galois_action_many(&pt_rs, &gsels).into_iter().for_each(|ptel| {
        //     smallP.println(&ptel); println!();});
        
        ////////////////////////////////// 

        // let ptslots = gen_random(&gbfv.slot_ring(), gbfv.pack(), None);
        // ptslots.iter().for_each(|el| gbfv.slot_ring().println(el));
        // println!("=================================");
        // let pt = gbfv.encode_slots_single_ref(ptslots.iter());

        // // let gsels = bigPgg.enumerate_elements().collect_vec();
        
        // let gsels = bigPgg.enumerate_elements().filter(|ggel| Zmsmall.is_one(&ZZ_to_Zmsmall.map(
        //     Zmbig.get_ring().any_lift(Zmbig.clone_el(bigPgg.as_ring_el(&ggel))) as i32
        // ))).collect_vec();

        // let pt_rs_big = bigP.apply_galois_action_many(&pt, &gsels).into_iter().fold(bigP.zero(),
        //     |acc, x| bigP.add(acc, x));

        // bigP.println(&pt_rs_big);
        // println!("=================================");

        // let pt_rs_slots = gbfv.decode_slots_single(pt_rs_big).collect_vec();
        // pt_rs_slots.iter().for_each(|el| gbfv.slot_ring().println(&el));
        // println!("=================================");

        // pt_rs_slots.iter().enumerate().filter_map(|(i, el)|
        //     ptslots.iter().any(|el2| gbfv.slot_ring().eq_el(el, el2)).then(|| (i, el)))
        //     .for_each(|(i, el)| println!("{i}: {}", gbfv.slot_ring().format(el)));

        // // let pt_rs = smallP.from_canonical_basis_extended(bigP.wrt_canonical_basis(&pt_rs_big).into_iter());

        // // gbfv_rs.decode_slots_single(pt_rs).for_each(|el| gbfv_rs.slot_ring().println(&el));
    }
}
