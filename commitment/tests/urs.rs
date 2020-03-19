/*****************************************************************************************************************

This source file, for now, implements URS unit test suite driver. The following tests are implemented:

1. urs_test
   This unit test generates a Universal Reference String for circuit depth of up to 20, computes its update and
   proceeds to the verification of URS update consistency against its zk-proof with the bilinear pairing map
   checks.

*****************************************************************************************************************/

use circuits::constraint_system::ConstraintSystem;
use colored::Colorize;
use commitment::urs::URS;
use pairing::bls12_381::Bls12;
use pairing::{Engine, Field, PrimeField};
use rand::OsRng;
use std::io;
use std::io::Write;
use std::time::Instant;

// The following test verifies the consistency of the
// URS generation with the pairings of the URS exponents
#[test]
fn urs_test() {
    test::<Bls12>();
    test_binary_compressed::<Bls12>();
    test_binary_uncompressed::<Bls12>();
}

#[allow(dead_code)]
fn progress(depth: usize) {
    print!("{:?}\r", depth);
    io::stdout().flush().unwrap();
}

fn test<E: Engine>() {
    let mut rng = OsRng::new().unwrap();
    let depth = 30;
    let iterations = 1;

    // generate sample URS string for circuit depth of up to 'depth'
    println!("{}", "Generating the initial URS".green());
    let mut start = Instant::now();
    let mut urs = URS::<E>::create(
        depth,
        vec![3, 7],
        E::Fr::from_str("11111").unwrap(),
        E::Fr::from_str("3333333").unwrap(),
    );
    println!("{}{:?}", "Execution time: ".yellow(), start.elapsed());

    for i in 0..iterations {
        println!("{}{:?}", "Iteration: ", i);
        println!("{}", "Computing the update of the URS".green());

        // save necessary URS elements to verify next update
        let hp1x1 = urs.hp1x1;
        let hpax0 = urs.hpax0;

        start = Instant::now();
        // update sample URS string for circuit depth of up to 'depth'
        urs.update(
            E::Fr::from_str("55555").unwrap(),
            E::Fr::from_str("7777777").unwrap(),
        );
        println!("{}{:?}", "Execution time: ".yellow(), start.elapsed());

        println!("{}", "Verifying the update against its zk-proof".green());
        start = Instant::now();
        assert_eq!(urs.check(hp1x1, hpax0, progress, &mut rng), true);
        println!("{}{:?}", "Execution time: ".yellow(), start.elapsed());
    }
}

fn test_binary_uncompressed<E: Engine>() {
    // field unity element
    let one = E::Fr::one();
    let mut neg1 = one;
    // field negative unit element
    neg1.negate();
    // Jubjub Edwards form coefficient d: y^2-x^2=1+d*y^2*x^2
    let d = E::Fr::from_str(
        "19257038036680949359750312669786877991949435402254120286184196891950884077233",
    )
    .unwrap();
    let mut negd = d;
    negd.negate();

    // our test circuit
    let mut cs = ConstraintSystem::<E::Fr>::create(3);
    cs.append('a', &[0], &[one]);
    cs.append('a', &[1], &[one]);
    cs.append('a', &[], &[]);
    cs.append('a', &[2], &[one]);
    cs.append('a', &[2], &[negd]);
    cs.append('b', &[0], &[neg1]);
    cs.append('b', &[1], &[neg1]);
    cs.append('b', &[2], &[one]);
    cs.append('b', &[], &[]);
    cs.append('b', &[2], &[one]);
    cs.append('c', &[], &[]);
    cs.append('c', &[], &[]);
    cs.append('c', &[1], &[negd]);
    cs.append('c', &[0], &[neg1]);
    cs.append('c', &[2], &[d]);
    cs.append_to_k(5, &[4], &[negd]);

    let field_element1 = E::Fr::from_str(
        "54799959613707685803997198407519087143449000911774710148164155636221645225006191",
    )
    .unwrap();
    let field_element2 = E::Fr::from_str(
        "36138681238004545275106256624762827227968497741908195957194228995387484282295954",
    )
    .unwrap();

    let mut start = Instant::now();

    let urs = URS::<E>::create_cs_based(&cs, field_element1, field_element2);

    println!("{}{:?}", "Generating URS time: ", start.elapsed());

    let g1_elements_count = urs.gp1x.len() + urs.gn1x.len() + urs.gpax.len() + urs.gnax.len();
    // hp1x1, hpax0, hpax1 are single G2 elements
    let g2_elements_count = urs.hn1x.len() + 3;
    let coordinates = g1_elements_count * 2 + g2_elements_count * 4;

    println!(
        "total G1 elements: {} G2: elements: {}, coordinates: {}",
        g1_elements_count, g2_elements_count, coordinates
    );

    let mut v = vec![];

    start = Instant::now();

    urs.write_uncompressed(&mut v).unwrap();

    println!(
        "{}{:?}",
        "Binary serializing time (uncompressed): ",
        start.elapsed()
    );

    std::fs::write("raw.urs", v.clone()).expect("unable to write into file");

    let attr = std::fs::metadata("raw.urs").unwrap();

    println!("Size: {} Mb", attr.len() / 1048576);

    let v = std::fs::read("raw.urs").unwrap();

    let start = Instant::now();

    let de_urs = URS::<E>::read_uncompressed(&v[..], false).unwrap();

    assert!(urs == de_urs);

    println!(
        "{}{:?}",
        "Binary deserializing time (uncompressed): ",
        start.elapsed()
    );
}

fn test_binary_compressed<E: Engine>() {
    // field unity element
    let one = E::Fr::one();
    let mut neg1 = one;
    // field negative unit element
    neg1.negate();
    // Jubjub Edwards form coefficient d: y^2-x^2=1+d*y^2*x^2
    let d = E::Fr::from_str(
        "19257038036680949359750312669786877991949435402254120286184196891950884077233",
    )
    .unwrap();
    let mut negd = d;
    negd.negate();

    // our test circuit
    let mut cs = ConstraintSystem::<E::Fr>::create(3);
    cs.append('a', &[0], &[one]);
    cs.append('a', &[1], &[one]);
    cs.append('a', &[], &[]);
    cs.append('a', &[2], &[one]);
    cs.append('a', &[2], &[negd]);
    cs.append('b', &[0], &[neg1]);
    cs.append('b', &[1], &[neg1]);
    cs.append('b', &[2], &[one]);
    cs.append('b', &[], &[]);
    cs.append('b', &[2], &[one]);
    cs.append('c', &[], &[]);
    cs.append('c', &[], &[]);
    cs.append('c', &[1], &[negd]);
    cs.append('c', &[0], &[neg1]);
    cs.append('c', &[2], &[d]);
    cs.append_to_k(5, &[4], &[negd]);

    let field_element1 = E::Fr::from_str(
        "54799959613707685803997198407519087143449000911774710148164155636221645225006191",
    )
    .unwrap();
    let field_element2 = E::Fr::from_str(
        "36138681238004545275106256624762827227968497741908195957194228995387484282295954",
    )
    .unwrap();

    let mut start = Instant::now();

    let urs = URS::<E>::create_cs_based(&cs, field_element1, field_element2);

    println!("{}{:?}", "Generating URS time: ", start.elapsed());

    let g1_elements_count = urs.gp1x.len() + urs.gn1x.len() + urs.gpax.len() + urs.gnax.len();
    // hp1x1, hpax0, hpax1 are single G2 elements
    let g2_elements_count = urs.hn1x.len() + 3;
    let coordinates = g1_elements_count * 2 + g2_elements_count * 4;

    println!(
        "total G1 elements: {} G2: elements: {}, coordinates: {}",
        g1_elements_count, g2_elements_count, coordinates
    );

    let mut v = vec![];

    start = Instant::now();

    urs.write_compressed(&mut v).unwrap();

    println!(
        "{}{:?}",
        "Binary serializing time (compressed): ",
        start.elapsed()
    );

    std::fs::write("raw.urs", v.clone()).expect("unable to write into file");

    let attr = std::fs::metadata("raw.urs").unwrap();

    println!("Size: {} Mb", attr.len() / 1048576);

    start = Instant::now();

    let de_urs = URS::<E>::read_compressed(&v[..], false).unwrap();

    assert!(urs == de_urs);

    println!(
        "{}{:?}",
        "Binary deserializing time (compressed): ",
        start.elapsed()
    );
}
