#![allow(non_snake_case)]

use feanor_math::ring::RingStore;

use proofs::util::matmul::{MatrixMul, DenseMatrixMul};
use easygbfv::tests::{
    get_gbfv_test, gen_random
};


fn main() {

    // Get a gbfv instance
    let gbfv = get_gbfv_test(0, 8, 100, None);
    
    let p = gbfv.pack(); // the number of slots in one ciphertext
    let slotring = gbfv.slot_ring(); // the ring that each slot element lives in

    // Generate the required secret keys
    let sk = gbfv.gen_sk();
    let pk = gbfv.gen_pk(&sk);

    let BLOCKROWS = 2;
    let BLOCKCOLUMNS = 2;

    // Sample a random input slot vector
    let slotsin = gen_random(&slotring, p*BLOCKCOLUMNS, Some("example_basic"));

    // Encrypt the slot vector into ciphertexts
    let ctin = gbfv.enc_slots_ref(slotsin.iter(), &sk);
    // Create object that represents a matrix-vector multplication
    let mm = DenseMatrixMul::new(slotring, p*BLOCKCOLUMNS, 
        gen_random(&slotring, p*BLOCKCOLUMNS*p*BLOCKROWS, Some("example_basic")), "example_basic");

    // Perform the matrix-vector multiplication in plaintext
    let mut slotsout = mm.mul(&slotsin);
    // Perform an element-wise squaring of the slotvector
    slotsout.iter_mut().for_each(|mut s| slotring.square(&mut s));

    // Perform the matrix-vector multiplication homomorphically
    let ctout_tmp = gbfv.hom_matmul(&mm, &ctin, &pk);
    // Perform the squaring homomorphically
    let ctout = gbfv.hom_square(ctout_tmp, &pk);

    // Print remaining noise budget
    println!("Output noise budget: {}", gbfv.noise_budget(&ctout, &sk));

    // Decrypt the output ciphertexts to a slot vector
    let slotsoutct = gbfv.dec_slots(ctout, &sk);

    // Print the output
    for (i, (out1, out2)) in slotsoutct.zip(slotsout.iter()).enumerate() {
        println!("Slot {}: {}, {}",
            i % p,
            slotring.format(&out1),
            slotring.format(out2)
        );
    }
}
