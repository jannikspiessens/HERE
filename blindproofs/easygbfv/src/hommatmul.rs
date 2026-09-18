use tracing::instrument;

use feanor_math::ring::*;
use feanor_math::homomorphism::{CanHom, CanHomFrom};
use feanor_math::group::AbelianGroupStore;
use fheanor::circuit::{PlaintextCircuit, Coefficient as FheanorCoefficient};
use fheanor::number_ring::galois::GaloisGroupEl;

use proofs::util::matmul::MatrixMul;

use crate::{
    gbfv::{GBFV, PlaintextRingBase, SlotRing},
};

type GGEl = GaloisGroupEl;
type Coefficient = FheanorCoefficient<PlaintextRingBase>;
type Circuit = crate::gbfv::PTCircuit;

pub struct HomMatrixMul<'a, R, MM, const LOG: bool, const BSGS: bool = true>
    where R: RingStore, <SlotRing as RingStore>::Type: CanHomFrom<<R as RingStore>::Type>,
          MM: MatrixMul<R = R>
{
    gbfv: &'a GBFV<LOG>,
    mm: &'a MM,
    hom: CanHom<&'a R, &'a SlotRing>
}

impl<'a, R, MM, const LOG: bool, const BSGS: bool> HomMatrixMul<'a, R, MM, LOG, BSGS>
    where R: RingStore, <SlotRing as RingStore>::Type: CanHomFrom<<R as RingStore>::Type>,
          MM: MatrixMul<R = R>
{

    pub fn new(mm: &'a MM, gbfv: &'a GBFV<LOG>) -> Self {
        Self {
            gbfv,
            mm,
            hom: gbfv.slot_ring().can_hom(mm.ring()).unwrap()
        }
    }

    #[instrument(skip_all)]
    pub fn circuit(&self) -> Circuit {
        let m = self.gbfv.pack();
        // TODO: remove this assertion
        assert!(self.mm.columns() % m == 0 && self.mm.rows() % m == 0);
        // TODO: use structure of matrix (eg SparseMatrixMul) to improve efficiency of circuits
        if self.mm.columns() != m || self.mm.rows() != m {
            let blockrows = self.mm.rows() / m;
            let blockcolumns = self.mm.columns() / m;
            if BSGS {
                self.circuit_block_bsgs(blockrows, blockcolumns)
            } else {
                self.circuit_block(blockrows, blockcolumns)
            }
        } else {
            if BSGS {
                self.circuit_noblock_bsgs()
            } else {
                self.circuit_noblock()
            }
        }
    }
    
    #[instrument(skip_all)]
    fn matmul_to_lintransform(&self, blockrows: usize, blockcolumns: usize)
        -> (Vec<GGEl>, Vec<Coefficient>)
    {
        let m = self.gbfv.pack();
        let pf = self.gbfv.native_pack_factor();
        let cggels = (0..m).map(|s| self.gbfv.get_rot_galois_el((m - s)*pf));
        let mut coeffs = Vec::with_capacity(blockrows*blockcolumns*m);
        for i in 0..blockrows {
            for j in 0..blockcolumns {
                coeffs.extend((0..m).map(|s| {
                    // Coefficient::Other(self.gbfv.encode_slots_bfv(
                    //         (0..m).map(|k|
                    //         self.mm.get_map(i*m + k, j*m + (k + s).rem_euclid(m), &self.hom)
                    //     ))
                    // )
                    let slots = (0..m).map(|k|
                        self.mm.get_map(i*m + k, j*m + (k + s).rem_euclid(m), &self.hom)
                    ).collect::<Vec<_>>();
                    self.gbfv.make_coefficient(slots)
                }));
            }
        }
        (cggels.collect(), coeffs)
    }

    #[instrument(skip_all)]
    pub fn circuit_noblock(&self) -> Circuit {

        let (galois_els, coeffs) = self.matmul_to_lintransform(1, 1);
        PlaintextCircuit::linear_transform(&coeffs, self.gbfv.plaintext_ring()).compose(
            PlaintextCircuit::gal_many(&galois_els,
                self.gbfv.hciso().galois_group(), self.gbfv.plaintext_ring()),
        self.gbfv.plaintext_ring())
    }

    #[instrument(skip_all)]
    pub fn circuit_block(&self, blockrows: usize, blockcolumns: usize) -> Circuit {

        let (galois_els, coeffs) = self.matmul_to_lintransform(blockrows, blockcolumns);
        let m = self.gbfv.pack();
        let ring = self.gbfv.hciso().ring();

        // for each input, take all galois automorphisms
        let mut current = PlaintextCircuit::empty();
        for _ in 0..blockcolumns {
            current = current.tensor(PlaintextCircuit::gal_many(
                &galois_els, self.gbfv.hciso().galois_group(), ring), ring);
        }

        // for each blockrow, do linear transform on galois automorphisms
        for (bind, brow) in coeffs.chunks_exact(blockcolumns*m).enumerate() {
            current = current.output_twice(ring);
            let lintrans = PlaintextCircuit::linear_transform(brow, ring);
            let dropper = PlaintextCircuit::identity(blockcolumns*m + bind, ring)
                .tensor(lintrans, ring)
                .tensor(PlaintextCircuit::drop(bind), ring);
            current = dropper.compose(current, ring);
        }
        
        // output an element for each blockrow
        PlaintextCircuit::drop(blockcolumns*m).tensor(
            PlaintextCircuit::identity(blockrows, ring), ring).compose(current, ring)
    }

    fn matmul_bsgs_parameters(&self) -> (usize, usize) {
        let m = self.gbfv.pack() as u64;
        // m is assumed to be a power of two
        let bs = m.isqrt().next_power_of_two();
        let gs = m / bs;
        //println!("bs: {}, gs: {}", bs, gs);
        assert!(gs * bs == m);
        (gs as usize, bs as usize)
    }

    fn matmul_bsgs_els(&self, a: usize, b: usize) -> (Vec<GGEl>, Vec<GGEl>)
    {
        let m = self.gbfv.pack();
        let pf = self.gbfv.native_pack_factor();

        let bs_galois_els: Vec<GGEl> =
            (0..b).map(|s| self.gbfv.get_rot_galois_el((m - s)*pf)).collect();
        let gs_galois_els: Vec<GGEl> =
            (0..a).map(|s| self.gbfv.get_rot_galois_el((m - s*b)*pf)).collect();

        (bs_galois_els, gs_galois_els)
    }

    #[instrument(skip_all)]
    fn matmul_bsgs_coeffs(&self, a: usize, b: usize, blockrows: usize, blockcolumns: usize)
        -> Vec<Coefficient>
    {
        let m = self.gbfv.pack() as i64;
        let (a, b) = (a as i64, b as i64);
    
        // ordering the coeffs according to usage in circuit generation
        (0..a).flat_map(|i|
            (0..blockrows as i64).flat_map(move |bi|
                (0..blockcolumns as i64).flat_map(move |bj| 
                    (0..b).map(move |j| {
                        let s = j + i*b;
                        let slots = (0..m).map(|k| self.mm.get_map(
                            (bi*m + (k - b*i).rem_euclid(m)) as usize,
                            (bj*m + (k + s - b*i).rem_euclid(m)) as usize,
                            &self.hom
                        )).collect::<Vec<_>>();
                        self.gbfv.make_coefficient(slots)
                    })
                )
            )
        ).collect()
    }

    #[instrument(skip_all)]
    fn circuit_noblock_bsgs(&self) -> Circuit
    {
        let (a, b) = self.matmul_bsgs_parameters();
        let (bs_gels, gs_gels) = self.matmul_bsgs_els(a, b);
        let coeffs = self.matmul_bsgs_coeffs(a, b, 1, 1);
        let ring = self.gbfv.hciso().ring();
        let galois_group = self.gbfv.hciso().galois_group();
        
        let bs_circuit = PlaintextCircuit::gal_many(&bs_gels, galois_group, ring);
        let mut current = PlaintextCircuit::constant(ring.zero(), ring).tensor(bs_circuit, ring);

        for (gs_gel, coeffs_chunk) in gs_gels.iter().zip(coeffs.chunks_exact(b)) {
            let lintrans = PlaintextCircuit::linear_transform(&coeffs_chunk, ring);
            let gal_of_lintrans = if galois_group.is_identity(gs_gel) {
                lintrans
            } else {
                PlaintextCircuit::gal(galois_group.clone_el(gs_gel), galois_group, ring).compose(lintrans, ring)
            };
            let acc_gsteps_circuit = PlaintextCircuit::add(ring).compose(
                PlaintextCircuit::identity(1, ring).tensor(
                    gal_of_lintrans,
                ring),
            ring);
            current = acc_gsteps_circuit.tensor(PlaintextCircuit::drop(1), ring).tensor(
                PlaintextCircuit::identity(b, ring), ring)
                    .compose(current.output_twice(ring), ring);
        }
        PlaintextCircuit::identity(1, ring).tensor(PlaintextCircuit::drop(b), ring)
            .compose(current, ring)
    }

    #[instrument(skip_all)]
    fn circuit_block_bsgs(&self, blockrows: usize, blockcolumns: usize) -> Circuit
    {
        let (a, b) = self.matmul_bsgs_parameters();
        let (bs_gels, gs_gels) = self.matmul_bsgs_els(a, b);
        let coeffs = self.matmul_bsgs_coeffs(a, b, blockrows, blockcolumns);
        let ring = self.gbfv.hciso().ring();
        let galois_group = self.gbfv.hciso().galois_group();

        let mut current = PlaintextCircuit::empty();
        // init constant zero wires
        for _ in 0..blockrows {
            current = current.tensor(PlaintextCircuit::constant(ring.zero(), ring), ring);
        }
        // for each input, take baby step galois automorphisms
        for _ in 0..blockcolumns {
            current = current.tensor(PlaintextCircuit::gal_many(
                &bs_gels, galois_group, ring), ring);
        }
        
        // for each giant step, do linear transforms over baby steps of each blockrow
        for (gs_gel, gs_chunk) in gs_gels.into_iter().zip(coeffs.chunks_exact(blockrows*blockcolumns*b))
        {
            current = current.output_times(blockrows + 1, ring);
            
            // for each blockrow, do linear transform over all baby steps
            let mut tmp = PlaintextCircuit::empty();
            for (i, brow_chunk) in gs_chunk.chunks_exact(blockcolumns*b).enumerate() {
                // linear transform over all baby step in the blockrow
                let lintrans = PlaintextCircuit::linear_transform(brow_chunk, ring);
                // giant step galois automorphism
                let mut brow_gal_of_lintrans = if galois_group.is_identity(&gs_gel) {
                    lintrans
                } else {
                    PlaintextCircuit::gal(galois_group.clone_el(&gs_gel), galois_group, ring).compose(lintrans, ring)
                };
                // drop unused wires created by `output_times`
                brow_gal_of_lintrans = if i == 0 {
                        PlaintextCircuit::identity(blockrows, ring)
                    } else {
                        PlaintextCircuit::drop(blockrows)
                    }.tensor(brow_gal_of_lintrans, ring);
                // place in aggregate tmp circuit
                tmp = tmp.tensor(brow_gal_of_lintrans, ring);
            }
            // add up outputs of giant steps
            tmp = PlaintextCircuit::vec_add(blockrows, ring).compose(tmp, ring);
            // place wires that will be inputs to next tmp circuit
            tmp = tmp.tensor(
                PlaintextCircuit::drop(blockrows).tensor(
                    PlaintextCircuit::identity(blockcolumns*b, ring), ring), ring);
            assert!(tmp.output_count() == blockrows + blockcolumns*b);
            assert!(tmp.input_count() == (blockrows + 1)*tmp.output_count());
            // compose to aggregate current circuit
            current = tmp.compose(current, ring);
        }
        // drop unused output wires
        PlaintextCircuit::identity(blockrows, ring)
            .tensor(PlaintextCircuit::drop(blockcolumns*b), ring)
            .compose(current, ring)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;
    use proofs::util::matmul::DenseMatrixMul;
    use crate::{LOG, tests::{get_gbfv_test, test_rot, gen_random}};

    fn test_gbfv_matmul_circuit<const BSGS: bool>(BLOCKROWS: usize, BLOCKCOLUMNS: usize) {

        // let pf = 1;
        let pf = 2;
        let gbfv = get_gbfv_test(0, 8, 100, Some(pf));

        let m = gbfv.pack();
        let slotring = gbfv.slot_ring();

        let slotsin = gen_random(&slotring, m*BLOCKCOLUMNS, None);
        
        let ptin = slotsin.iter().chunks(m).into_iter().map(|chunk_of_slots|
            gbfv.encode_slots_single_ref(chunk_of_slots)).collect::<Vec<_>>();

        let seed = format!("test_matmul_{}BSGS_{}{}_pf{}",
                if BSGS {"with"} else {"no"}, BLOCKROWS, BLOCKCOLUMNS, pf);
        let mm = DenseMatrixMul::new(slotring, m*BLOCKCOLUMNS, 
            gen_random(&slotring, m*BLOCKCOLUMNS*m*BLOCKROWS, Some(&seed)), &seed);

        let hmm = HomMatrixMul::<SlotRing, DenseMatrixMul<SlotRing>, LOG, {BSGS}>::new(&mm, &gbfv);
        let circuit = gbfv.read_or_create_circuit(gbfv.plaintext_ring(), mm.desc(),
            || hmm.circuit());

        println!("Circuit stats:");
        println!("Input count: {}", circuit.input_count());
        println!("Output count: {}", circuit.output_count());
        println!("");

        let slotsout = mm.mul(&slotsin);

        let ptout = circuit.evaluate(&ptin[..], gbfv.plaintext_ring().identity());
        let slotsoutpt = ptout.into_iter().flat_map( |ptoutel| 
            gbfv.decode_slots_single(ptoutel)).collect::<Vec<_>>();

        assert!(mm.rows() == slotsout.len());
        assert!(mm.columns() == slotsin.len());
        
        test_rot(&gbfv.slot_ring(), &slotsoutpt, &slotsout, 0);
    }

    #[test]
    fn test_gbfv_matmul_noblock_circuit_nobsgs() {
        test_gbfv_matmul_circuit::<false>(1, 1)
    } 

    #[test]
    fn test_gbfv_matmul_block_circuit_nobsgs() {
        test_gbfv_matmul_circuit::<false>(3, 2)
    } 

    #[test]
    fn test_gbfv_matmul_noblock_circuit_bsgs() {
        test_gbfv_matmul_circuit::<true>(1, 1)
    } 

    #[test]
    fn test_gbfv_matmul_block_circuit_bsgs() {
        test_gbfv_matmul_circuit::<true>(5, 3)
    } 
}

