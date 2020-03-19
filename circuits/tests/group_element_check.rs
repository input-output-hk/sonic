/*****************************************************************************************************************

This source file implements Sonic Constraint System unit test suite driver. The following tests are implemented:

1. Checking Point to be a Group Element
   This test implements the constraint system as per section 4.2.1 of circuits.pdf document. The
   Curve constrained computation verifies if an element (given by its Edwards coordinates) belongs to the
   Elliptic Curve group. The test runs the verification that check that a witness (given by its Edwards
   coordinates) satisfies the constraint equations.

    For the wire labels

    a=[y, x, yy]
    b=[y, x, dxx]
    c= [yy, xx, yy-xx-1]

    the linear constraint system is:

    u= [[ 1, 0, 0], [0,  1, 0], [0,  0, 0], [ 0, 0, 1], [0, 0, -d]]
    v= [[-1, 0, 0], [0, -1, 0], [0,  0, 1], [ 0, 0, 0], [0, 0,  1]]
    w= [[ 0, 0, 0], [0,  0, 0], [0, -d, 0], [-1, 0, 0], [0, 0,  d]]
    k= [0, 0, 0, 0, -d]

    The test verifies both positive and negative outcomes for satisfying and not satisfying witnesses

*****************************************************************************************************************/

use circuits::constraint_system::{ConstraintSystem, Witness};
use circuits::gate::CircuitGate;
use pairing::{bls12_381::Bls12, Engine, Field, PrimeField};
use rand::OsRng;
use sprs::CsVec;

// The following test verifies the polynomial commitment scheme
#[test]
fn constraints_test() {
    group_element_test::<Bls12>();
}

fn group_element_test<E: Engine>() {
    let mut rng = OsRng::new().unwrap();

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
    // our circuit cinstraint system
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

    // We have the constraint system. Let's choose an example satisfying witness for Jubjub y^2-x^2=1+d*y^2*x^2
    let x = E::Fr::from_str(
        "47847771272602875687997868466650874407263908316223685522183521003714784842376",
    )
    .unwrap();
    let y = E::Fr::from_str(
        "14866155869058627094034298869399931786023896160785945564212907054495032619276",
    )
    .unwrap();

    // check whether the point is on the curve
    let mut xx = x;
    let mut yy = y;
    xx.square();
    yy.square();
    let mut yy_xx_1 = yy;
    yy_xx_1.sub_assign(&xx);
    yy_xx_1.sub_assign(&one);
    let mut dxx = d;
    dxx.mul_assign(&xx);
    let mut dxxyy = dxx;
    dxxyy.mul_assign(&yy);
    assert_eq!(yy_xx_1, dxxyy);

    /*
    the point is on the curve, let's compute the witness and verify the circuit satisfiability
        Wire labels
        a=[y, x, yy]
        b=[y, x, dxx]
        c= [yy, xx, yy-xx-1]
    */
    let mut witness = Witness::<E::Fr>::create(3, &mut rng);
    witness.gates[0] = CircuitGate::<E::Fr> { a: y, b: y, c: yy };
    witness.gates[1] = CircuitGate::<E::Fr> { a: x, b: x, c: xx };
    witness.gates[2] = CircuitGate::<E::Fr> {
        a: yy,
        b: dxx,
        c: yy_xx_1,
    };

    // verify the circuit satisfiability by the computed witness
    assert_eq!(cs.verify(None, &witness), true);

    // The computation circuit is satisfied by the witness
    // Now let's chose invalid witness by changing just one digit

    let x = E::Fr::from_str(
        "57847771272602875687997868466650874407263908316223685522183521003714784842376",
    )
    .unwrap();
    let y = E::Fr::from_str(
        "14866155869058627094034298869399931786023896160785945564212907054495032619276",
    )
    .unwrap();

    // check whether the point is on the curve
    let mut xx = x;
    let mut yy = y;
    xx.square();
    yy.square();
    let mut yy_xx_1 = yy;
    yy_xx_1.sub_assign(&xx);
    yy_xx_1.sub_assign(&one);
    let mut dxx = d;
    dxx.mul_assign(&xx);
    let mut dxxyy = dxx;
    dxxyy.mul_assign(&yy);
    assert_ne!(yy_xx_1, dxxyy);

    /*
    the point is not on the curve, let's compute the witness and verify the circuit satisfiability
        Wire labels
        a=[y, x, yy]
        b=[y, x, dxx]
        c= [yy, xx, yy-xx-1]
    */
    let mut witness = Witness::<E::Fr>::create(3, &mut rng);
    witness.gates[0] = CircuitGate::<E::Fr> { a: y, b: y, c: yy };
    witness.gates[1] = CircuitGate::<E::Fr> { a: x, b: x, c: xx };
    witness.gates[2] = CircuitGate::<E::Fr> {
        a: yy,
        b: dxx,
        c: yy_xx_1,
    };

    // verify the circuit satisfiability by the computed witness
    assert_eq!(cs.verify(None, &witness), false);

    // The computation circuit is not satisfied by the witness
}
