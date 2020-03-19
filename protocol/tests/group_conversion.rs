/***************************************************************************************************

This source file implements Sonic's zk-proof primitive unit test suite driver.
The following tests are implemented:

1.
   This tests batch of Sonic statement proofs as per section 4.2.5 of circuits.pdf document.
   The Jubjub constrained computation verifies if an array of EC points (given by Edwards
   coordinates) belongs to the Elliptic Curve group. First, the test verifies that the witness array
   satisfies the constraint equations. Second, it computes and verifies the Sonic KZ-proofs of all
   the statements (against the constraint system). The proof batch consists of Sonic zk-proofs, each
   of them proving, in zero-knowledge, that a point in the array of EC points belongs to the Jubjub
   EC group.

    For the wire labels

    a = [x, y]
    b = [v, u+1]
    c = [sqrt(-40964)*u, u-1]

    the linear constraint system is:

    u= [[0,0],[0,0]]
    v= [[0,1],[0,-sqrt(-40964)]]
    w= [[0,-1],[1,0]]
    k= [2,-sqrt(-40964)]

    The test verifies both positive and negative outcomes for satisfying and not satisfying
    witnesses.

***************************************************************************************************/
use circuits::constraint_system::{CircuitGate, ConstraintSystem, Witness};
use commitment::urs::URS;
use pairing::{bls12_381::Bls12, Engine, Field, PrimeField};
use polynomials::univariate::Univariate;
use protocol::batch::{BatchProof, ProverProof};
use rand::OsRng;
use sprs::CsVec;

#[test]
fn group_conversion_test() {
    test::<Bls12>();
}

#[allow(non_snake_case)]
fn test<E: Engine>() {
    let mut rng = OsRng::new().unwrap();
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

    let depth = cs.k.dim() + 4 * cs.a.shape().1 + 8;

    // generate sample URS
    let urs = URS::<E>::create(
        depth,
        vec![
            depth,
            cs.a.shape().1 + 1,
            cs.a.shape().1 * 2 + 1,
            cs.a.shape().1 + cs.a.shape().0 + 1,
        ],
        Univariate::<E::Fr>::rand(&mut rng),
        Univariate::<E::Fr>::rand(&mut rng),
    );

    positive::<E>(&urs, &cs, &mut rng);
    negative::<E>(&urs, &cs, &mut rng);
}

#[allow(non_snake_case)]
fn positive<E: Engine>(urs: &URS<E>, cs: &ConstraintSystem<E::Fr>, rng: &mut OsRng) {
    // We have the constraint system. Let's choose examples of satisfying witness for Jubjub y^2-x^2=1+d*y^2*x^2
    let mut points = Vec::<(E::Fr, E::Fr, E::Fr, E::Fr)>::new();
    let mut witness_batch = Vec::<Witness<E::Fr>>::new();
    let one = E::Fr::one();
    let sqrtmjjA = E::Fr::from_str(
        "17814886934372412843466061268024708274627479829237077604635722030778476050649",
    )
    .unwrap();

    points.push((
        E::Fr::from_str(
            "853554559207543847252664416966410582098606963183071025729253243887385698701",
        )
        .unwrap(),
        E::Fr::from_str(
            "14764243698000945526787211915034316971081786721517742096668223329470205650604",
        )
        .unwrap(),
        E::Fr::from_str(
            "49792417373762009466546315427310015213131913431044267875338124358756912689577",
        )
        .unwrap(),
        E::Fr::from_str(
            "18704088696874163653775932556954898929880637695754080357664668755728034697568",
        )
        .unwrap(),
    ));

    // check whether the points are on the curve
    for i in 0..points.len() {
        let (x, y, u, v) = points[i];
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

        let mut witness = Witness::<E::Fr>::create(2, rng);
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
        // add the witness to the batch
        witness_batch.push(witness);
    }

    // The computation circuit is satisfied by the witness array
    // Now let's create zk-proof batch of the statements

    let s = String::from("In the blockchain setting this has to come from the block context");
    let batch_context: Vec<u8> = s.into_bytes();
    let mut prover_proofs = Vec::<(ProverProof<E>, Option<CsVec<E::Fr>>)>::new();

    // create the vector of prover's proofs for the given witness vector
    for i in 0..points.len() {
        match ProverProof::<E>::create(&witness_batch[i], &cs, None, &urs) {
            Err(error) => {
                panic!("Failure creating the prover's proof: {}", error);
            }
            Ok(proof) => prover_proofs.push((proof, None)),
        }
    }

    // create and verify the batch of zk-proofs for the given witness vector
    match BatchProof::<E>::create(&batch_context, &prover_proofs, &cs, &urs, rng) {
        Err(error) => {
            panic!(error);
        }
        Ok(mut batch) => {
            for i in 0..batch.batch.len() {
                match &batch.batch[i].helper {
                    Err(error) => {
                        panic!("Failure verifying the prover's proof: {}", error);
                    }
                    Ok(_) => continue,
                }
            }
            match batch.verify(&batch_context, &cs, &vec![None; batch.batch.len()], &urs, rng) {
                Err(_) => {
                    panic!("Failure verifying the zk-proof");
                }
                Ok(_) => {
                    // we expect exit here on successful proof verification, since test is positive
                }
            }
        }
    }
}

#[allow(non_snake_case)]
fn negative<E: Engine>(urs: &URS<E>, cs: &ConstraintSystem<E::Fr>, rng: &mut OsRng) {
    // We have the constraint system. Let's choose examples of satisfying witness for Jubjub y^2-x^2=1+d*y^2*x^2
    let mut points = Vec::<(E::Fr, E::Fr, E::Fr, E::Fr)>::new();
    let mut witness_batch = Vec::<Witness<E::Fr>>::new();
    let one = E::Fr::one();
    let sqrtmjjA = E::Fr::from_str(
        "17814886934372412843466061268024708274627479829237077604635722030778476050649",
    )
    .unwrap();

    // witness that does not satisfy the statement
    points.push((
        E::Fr::from_str(
            "853554559207543847252664416966410582098606963183071025729253243887385698701",
        )
        .unwrap(),
        E::Fr::from_str(
            "14764243698000945526787211915034316971081786721517742096668223329470205650604",
        )
        .unwrap(),
        E::Fr::from_str(
            "49792417373762009466546315427310015213131913431044267875338124358756912689577",
        )
        .unwrap(),
        E::Fr::from_str(
            "1", // wrong value
        )
        .unwrap(),
    ));

    // check whether the points are on the curve
    for i in 0..points.len() {
        let (x, y, u, v) = points[i];
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

        let mut witness = Witness::<E::Fr>::create(2, rng);
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

        // add the witness to the batch
        witness_batch.push(witness);
    }

    // The computation circuit is satisfied by the witness array
    // Now let's create zk-proof batch of the statements
    let s = String::from("In the blockchain setting this has to come from the block context");
    let batch_context: Vec<u8> = s.into_bytes();
    let mut prover_proofs = Vec::<(ProverProof<E>, Option<CsVec<E::Fr>>)>::new();

    // create the vector of prover's proofs for the given witness vector
    for i in 0..points.len() {
        match ProverProof::<E>::create(&witness_batch[i], &cs, None, &urs) {
            Err(error) => {
                panic!("Failure creating the prover's proof: {}", error);
            }
            Ok(proof) => prover_proofs.push((proof, None)),
        }
    }

    // create and verify the batch of zk-proofs for the given witness vector
    match BatchProof::<E>::create(&batch_context, &prover_proofs, &cs, &urs, rng) {
        Err(error) => {
            panic!(error);
        }
        Ok(mut batch) => {
            for i in 0..batch.batch.len() {
                match &batch.batch[i].helper {
                    Err(_) => {}
                    Ok(_) => {
                        panic!("Failure invalidating the prover's proof");
                    }
                }
            }
            match batch.verify(&batch_context, &cs, &vec![None; batch.batch.len()], &urs, rng) {
                Err(_) => {
                    // we expect exit here on proof verification error, since test is negative
                }
                Ok(_) => {
                    panic!("Failure invalidating the zk-proof");
                }
            }
        }
    }
}
