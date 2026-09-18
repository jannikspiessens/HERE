use feanor_math::homomorphism::{CanHom, CanHomFrom};
use feanor_math::ring::{El, RingStore};
use feanor_math::field::{Field, FieldStore};
use fheanor::circuit::Coefficient;

use proofs::util::{int_from_bits, bits_from_int, bits, matmul::SparseMatrixMul};
use easygbfv::{
    gbfv::{
        GBFV, PublicKey, SlotRing, CTCircuit, PTCircuit,
        Ciphertext as Ct
    },
    hommatmul::HomMatrixMul
};


pub mod sumcheck;

// pub mod spartan;

pub mod vMM;

pub fn ctcoeffs_to_ctevals_packonly_circuit_shallow<const LOG: bool>(gbfv: &GBFV<LOG>,
    logpack: usize, logsize: usize, reverse: bool) -> CTCircuit
{
    let slotring = gbfv.slot_ring();
    let logtot = logpack + logsize;
    let data = bits(logtot).map(|bi| {
        let i = int_from_bits(bi.clone().into_iter());
        let start = (i + 1).checked_sub(1 << logpack).unwrap_or_default() ;
        (start..=i).map(|j| {
            let bj = bits_from_int(j, logtot);
            let negone = if reverse { bi.iter().zip(bj.clone()).filter(|(bik, bjk)|
                **bik == 1 && *bjk == 0).count() % 2 == 1
            } else { false };
            let el = if bi.iter().zip(bj).any(|(bik, bjk)| *bik == 0 && bjk == 1 )
                { slotring.zero() } else { if negone {slotring.neg_one()} else {slotring.one()}};
            (j, el)
        }).collect()
    }).collect();
    let mm = SparseMatrixMul::new(slotring, 1 << logtot , data,
        &format!("multilinearV_{}", logtot));
    gbfv.lift_circuit(HomMatrixMul::<_, _, LOG>::new(&mm, gbfv).circuit())
}

pub fn ctcoeffs_to_ctevals_packonly_circuit_deep<const LOG: bool>(gbfv: &GBFV<LOG>,
    logpack: usize, logsize: usize, reverse: bool) -> CTCircuit
{
    let slotring = gbfv.slot_ring();
    let ring = gbfv.hciso().ring();
    let gg = gbfv.hciso().galois_group();
    let id = PTCircuit::identity(1 << logsize, ring);

    let mut res = id.clone(ring);
    for i in 0..logpack {
        let coeff = Coefficient::Other(gbfv.encode_slots_single((0..(1 << logpack)).map(|j|
            if (j >> i) & 1 == 1 { slotring.one() } else { slotring.zero() })));
        let galmask = PTCircuit::linear_transform(&[coeff], ring).compose(
            PTCircuit::gal(gbfv.get_rot_galois_el(1 << i), gg, ring), ring);

        let mut tmp = PTCircuit::empty();
        for _ in 0..(1 << logsize) {
            tmp = tmp.tensor(galmask.clone(ring), ring);
        }
        tmp = id.clone(ring).tensor(tmp, ring);

        res = tmp.compose(res.output_twice(ring), ring);
        res = if reverse { PTCircuit::vec_sub(1 << logsize, ring) }
            else { PTCircuit::vec_add(1 << logsize, ring) }.compose(res, ring);
    }
    gbfv.lift_circuit(res)
}

pub fn ctcoeffs_to_ctevals<const LOG: bool>(gbfv: &GBFV<LOG>, logpack: usize,
    logsize: usize, ctcoeffs: &[Ct], pk: &PublicKey, reverse: bool, deep: bool) -> Vec<Ct>
{
    debug_assert!(gbfv.pack() == 1 << logpack);
    // Noise difference seems to be minimal, so faster deep method is preferred?
    
    let get_circuit = || {
        let ring = gbfv.ciphertext_ring();

        // Performs transformation inside of packing only
        let mut res = if deep {
            ctcoeffs_to_ctevals_packonly_circuit_deep(gbfv, logpack, logsize, reverse)
        } else {
            // TODO: ideally, we could simply define the matrix to have repeating blocks and then
            // the hommatrixmul circuits would only perform the Mv product for the block once
            ctcoeffs_to_ctevals_packonly_circuit_shallow(gbfv, logpack, logsize, reverse)
        };

        // Performs transformation outside of packing
        for i in 0..logsize {
            let mut tmp = CTCircuit::empty();
            for _ in 0..(1 << (logsize - i  - 1)) {
                tmp = tmp.tensor(if reverse { CTCircuit::fold_sub(1 << i, ring) } else {
                    CTCircuit::fold_add(1 << i, ring)
                }, ring);
            }
            res = res.compose(tmp, ring);
        }
        res
    };

    let circname = if reverse {
        format!("ctevals_to_ctcoeffs_circuit_{}{}{}", logpack, logsize,
            if deep {"deep"} else {"shallow"})
    } else {
        format!("ctcoeffs_to_ctevals_circuit_{}{}{}", logpack, logsize,
            if deep {"deep"} else {"shallow"})
    };
    let circuit = gbfv.read_or_create_circuit(gbfv.ciphertext_ring(), &circname, get_circuit);
    
    gbfv.evaluate_circuit_small(&circuit, ctcoeffs, pk)
}


pub fn univar_evaluate_at_fromctcoeff<'a, F, const LOG: bool>(gbfv: &'a GBFV<LOG>, field: &F,
    hom: &CanHom<&'a F, &'a SlotRing>, ctcoeffs: &[Ct], at: &El<F>) -> Ct
    where F: FieldStore<Type: Field>,
          <SlotRing as RingStore>::Type: CanHomFrom<<F as RingStore>::Type>
{
    ctcoeffs.into_iter().enumerate().fold(gbfv.ct_zero(), |acc, (i, ct)|
        gbfv.hom_add_single(acc, gbfv.hom_mul_plainslot_single_map(ct,
            field.pow(field.clone_el(at), i), hom)))
}


pub fn multilinear_evaluate_at_fromctcoeff<'a, F, const LOG: bool>(gbfv: &'a GBFV<LOG>, field: &F,
    hom: &CanHom<&'a F, &'a SlotRing>, ctcoeffs: &[Ct], at: &[El<F>]) -> Vec<Ct>
    where F: RingStore<Type: Field>,
          <SlotRing as RingStore>::Type: CanHomFrom<<F as RingStore>::Type>
{
    assert!(ctcoeffs.len().is_power_of_two());
    let logctcoeffslen = ctcoeffs.len().ilog2() as usize;
    // TODO: allow code.generator().columns() to divide gbfv.pack()
    assert!(logctcoeffslen >= at.len());
    let logreslen = logctcoeffslen - at.len();
    bits(logreslen).map(|bi|
        bits(at.len()).fold(gbfv.ct_zero(), |acc, bj| {
            let scalar = bj.iter().enumerate().filter(|(_, x)| **x == 1)
                .fold(field.one(), |a, (k, _)| field.mul_ref_snd(a, &at[k]));
            let ind = int_from_bits([bi.clone(), bj].concat().into_iter());
            let tmp = gbfv.hom_mul_plainslot_single_map(&ctcoeffs[ind], scalar, hom);
            gbfv.hom_add_single(acc, tmp)
        })
    ).collect()
}


#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::rings::finite::FiniteRingStore;
    use proofs::multilinear::{coeffs_to_evals_inplace, evals_to_coeffs_inplace};
    use proofs::util::gen_vector;
    use easygbfv::{gbfv::SlotField, tests::get_gbfv_test};
    use crate::util::tests::test_correctness;

    fn test_ctcoeffs_to_ctevals_opt(reverse: bool, deep: bool) {
        let gbfv = get_gbfv_test(0, 8, 400, None);
        let sk = gbfv.gen_sk();
        let pk = gbfv.gen_pk(&sk);
        let slotfield = gbfv.slot_field();
        let hom = gbfv.slot_ring().can_hom(&slotfield).unwrap();

        let logpack = gbfv.pack().ilog2() as usize;
        let N = logpack + 2;

        let one = gen_vector::<El<SlotField>>(||
            slotfield.random_element(rand::random::<u64>), 1 << N);
        let mut two = one.iter().map(|c| slotfield.clone_el(c)).collect::<Vec<_>>();
        if reverse {
            evals_to_coeffs_inplace(&slotfield, N, &mut two);
        } else {
            coeffs_to_evals_inplace(&slotfield, N, &mut two);
        }

        let ctin = gbfv.enc_slots_map(one.into_iter(), &hom, &sk);

        println!("Input noise budget: {}", gbfv.noise_budget(&ctin, &sk));

        let ctout = ctcoeffs_to_ctevals(&gbfv, logpack, N - logpack, &ctin, &pk, reverse, deep);

        println!("Output noise budget: {}", gbfv.noise_budget(&ctout, &sk));

        test_correctness(&gbfv, &slotfield, &sk, ctout, two, &hom);
    }

    #[test]
    fn test_ctcoeffs_to_ctevals_shallow() {
        test_ctcoeffs_to_ctevals_opt(false, false)
    }

    #[test]
    fn test_ctcoeffs_to_ctevals_deep() {
        test_ctcoeffs_to_ctevals_opt(false, true)
    }

    #[test]
    fn test_ctevals_to_ctcoeffs_shallow() {
        test_ctcoeffs_to_ctevals_opt(true, false)
    }

    #[test]
    fn test_ctevals_to_ctcoeffs_deep() {
        test_ctcoeffs_to_ctevals_opt(true, true)
    }
}

