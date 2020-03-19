/*****************************************************************************************************************

This source file implements Sonic Constraint System unit test suite driver. The following tests are implemented:

1. Checking Point conversion formula between Edwards and Montgomery coordinates.
   This test implements the constraint system as per section 4.2.5 of circuits.pdf document.

    For the wire labels

    a = [x, y]
    b = [v, u+1]
    c = [sqrt(-40964)*u, u-1]

    the linear constraint system is:

    u= [[0,0],[0,0]]
    v= [[0,1],[0,-sqrt(-40964)]]
    w= [[0,-1],[1,0]]
    k= [2,-sqrt(-40964)]

    The test verifies both positive and negative outcomes for satisfying and not satisfying witnesses

*****************************************************************************************************************/

use circuits::constraint_system::{CircuitGate, ConstraintSystem, Witness};
use pairing::{bls12_381::Bls12, Engine, Field, PrimeField};
use rand::OsRng;
use sprs::CsVec;

// The following test verifies the addition of jubjub points
#[test]
fn constraints_test() {
    group_convert_test::<Bls12>();
}

#[allow(non_snake_case)]
fn group_convert_test<E: Engine>() {
    let mut rng = OsRng::new().unwrap();

    // initialise constants

    // field zero element
    let zero = E::Fr::zero();
    // field unity element
    let one = E::Fr::one();
    let mut neg1 = one;
    // field negative unit element
    neg1.negate();
    let two = E::Fr::from_str("2").unwrap();
    let negsqrtmjjA = E::Fr::from_str(
        "34620988240753777635981679240161257563063072671290560217967936669160105133864",
    )
    .unwrap();
    let sqrtmjjA = E::Fr::from_str(
        "17814886934372412843466061268024708274627479829237077604635722030778476050649",
    )
    .unwrap();
    // Jubjub Edwards form coefficient d: y^2-x^2=1+d*y^2*x^2
    let d = E::Fr::from_str(
        "19257038036680949359750312669786877991949435402254120286184196891950884077233",
    )
    .unwrap();
    let mut negd = d;
    negd.negate();

    // our circuit cinstraint system
    let mut cs = ConstraintSystem::<E::Fr>::create(2);
    cs.b.insert(0, 1, one);
    cs.c.insert(0, 1, neg1);
    cs.c.insert(1, 0, one);
    cs.b.insert(1, 1, negsqrtmjjA);
    cs.a.insert(0, 0, zero);
    cs.a.insert(1, 0, zero);

    let inds = vec![0, 1];
    let vals = vec![two, negsqrtmjjA];
    cs.k = CsVec::<E::Fr>::new(2, inds, vals);

    // We have the constraint system. Let's choose points (x,y) and (u,v)
    // correspond to their addition
    let x = E::Fr::from_str(
        "853554559207543847252664416966410582098606963183071025729253243887385698701",
    )
    .unwrap();
    let y = E::Fr::from_str(
        "14764243698000945526787211915034316971081786721517742096668223329470205650604",
    )
    .unwrap();
    let u = E::Fr::from_str(
        "49792417373762009466546315427310015213131913431044267875338124358756912689577",
    )
    .unwrap();
    let v = E::Fr::from_str(
        "18704088696874163653775932556954898929880637695754080357664668755728034697568",
    )
    .unwrap();

    // check whether the point is on the curve
    /*
        a = [x, y]
        b = [v, u+1]
        c = [sqrt(-40964)*u, u-1]
    */
    let mut up1 = u;
    up1.add_assign(&one);
    let mut um1 = u;
    um1.sub_assign(&one);
    let mut xv = x;
    xv.mul_assign(&v);
    let mut yup1 = y;
    yup1.mul_assign(&up1);
    let mut sqrtmjjAu = sqrtmjjA;
    sqrtmjjAu.mul_assign(&u);
    assert_eq!(xv, sqrtmjjAu);
    assert_eq!(yup1, um1);

    /*
    the point (x,y) in Edwards coordinates corresponds to point (u,v) in Montgomery coordinates.
        Wire labels
        a = [x, y]
        b = [v, u+1]
        c = [sqrt(-40964)*u, u-1]
    */
    let mut witness = Witness::<E::Fr>::create(2, &mut rng);
    witness.gates[0] = CircuitGate::<E::Fr> {
        a: x,
        b: v,
        c: sqrtmjjAu,
    };
    witness.gates[1] = CircuitGate::<E::Fr> {
        a: y,
        b: up1,
        c: um1,
    };

    // verify the circuit satisfiability by the computed witness
    assert_eq!(cs.verify(None, &witness), true);
}
