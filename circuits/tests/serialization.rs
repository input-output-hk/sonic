use circuits::constraint_system::ConstraintSystem;
use pairing::{bls12_381::Bls12, Engine, Field, PrimeField};
use sprs::CsVec;

#[test]
fn constraints_system_serialization_test() {
    simple_test::<Bls12>();
}

fn simple_test<E: Engine>() {
    // initialise constants
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

    /*
        u= [[ 1, 0, 0], [0,  1, 0], [0,  0, 0], [ 0, 0, 1], [0, 0, -d]]
        v= [[-1, 0, 0], [0, -1, 0], [0,  0, 1], [ 0, 0, 0], [0, 0,  1]]
        w= [[ 0, 0, 0], [0,  0, 0], [0, -d, 0], [-1, 0, 0], [0, 0,  d]]
        k= [0, 0, 0, 0, -d]
    */
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
    cs.k = CsVec::<E::Fr>::new(5, vec![4], vec![negd]);

    let mut v = vec![];
    cs.write(&mut v).unwrap();

    let de_cs = ConstraintSystem::<E::Fr>::read(&v[..]).unwrap();
    assert_eq!(cs, de_cs);
}
