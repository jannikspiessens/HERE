
#[cfg(test)]
pub mod tests {
    use feanor_math::ring::{El, RingStore};
    use feanor_math::homomorphism::{CanHom, CanHomFrom, Homomorphism};
    use feanor_math::rings::field::AsField;
    use easygbfv::gbfv::{GBFV, Ciphertext, SlotRing, SecretKey};
    use easygbfv::tests::test_rot;

    pub type SlotField = AsField<SlotRing>;

    pub fn test_correctness_ref<R, const LOG: bool>(gbfv: &GBFV<LOG>, ring: &R, sk: &SecretKey,
        cts: Vec<Ciphertext>, pts: &[El<R>], hom: &CanHom<&R, &SlotRing>)
        where R: RingStore, <SlotRing as RingStore>::Type: CanHomFrom<<R as RingStore>::Type>
    {
        test_correctness(gbfv, ring, sk, cts,
            pts.iter().map(|el| ring.clone_el(el)).collect(), hom);
    }

    pub fn test_correctness<R, const LOG: bool>(gbfv: &GBFV<LOG>, ring: &R, sk: &SecretKey,
        cts: Vec<Ciphertext>, pts: Vec<El<R>>, hom: &CanHom<&R, &SlotRing>)
        where R: RingStore, <SlotRing as RingStore>::Type: CanHomFrom<<R as RingStore>::Type>
    {
        let dec = gbfv.dec_slots(cts, &sk).collect::<Vec<_>>();
        dec.iter().zip(pts.iter()).enumerate().for_each(|(i, (d, p))|
            println!("{} {} {} {}", i,
                gbfv.slot_ring().format(d),
                ring.format(p),
                gbfv.slot_ring().eq_el(d, &hom.map_ref(p)))
        );
        test_rot(gbfv.slot_ring(), &dec, &pts.into_iter().map(|el| hom.map(el)).collect(), 0);
    }
}
