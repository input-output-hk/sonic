/***************************************************************************************************

This source file implements Sonic's zk-proof primitive unit test suite driver.
The following tests are implemented:

1.
   This tests batch of Sonic statement proofs as per section 4.2.1 of circuits.pdf document.
   The Jubjub constrained computation verifies if an array of EC points (given by Edwards
   coordinates) belongs to the Elliptic Curve group. First, the test verifies that the witness array
   satisfies the constraint equations. Second, it computes and verifies the Sonic ZK-proofs of all
   the statements (against the constraint system). The proof batch consists of Sonic zk-proofs, each
   of them proving, in zero-knowledge, that a point in the array of EC points belongs to the Jubjub
   EC group.

    For the wire labels

    a=[y, x, yy]
    b=[y, x, dxx]
    c= [yy, xx, yy-xx-1]

    the linear constraint system is:

    u= [[1, 0, 0], [0, 1, 0], [0, 0, 0], [0, 0, 1], [0, 0, -d]]
    v= [[-1, 0, 0], [0, -1, 0], [0, 0, 1], [0, 0, 0], [0, 0, 1]]
    w= [[0, 0, 0], [0, 0, 0], [0, -d, 0], [-1, 0, 0], [0, 0, d]]
    k= [0, 0, 0, 0, -d]

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
fn group_element_check_test() {
    test::<Bls12>();
}

fn test<E: Engine>() {
    let mut rng = OsRng::new().unwrap();
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

    // generate sample URS
    let depth = cs.k.dim() + 4 * cs.a.shape().1 + 8;
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

fn positive<E: Engine>(urs: &URS<E>, cs: &ConstraintSystem<E::Fr>, rng: &mut OsRng) {
    let d = E::Fr::from_str(
        "19257038036680949359750312669786877991949435402254120286184196891950884077233",
    )
    .unwrap();

    // We have the constraint system. Let's choose examples of satisfying witness for Jubjub y^2-x^2=1+d*y^2*x^2
    let mut points = Vec::<(E::Fr, E::Fr)>::new();
    let mut witness_batch = Vec::<Witness<E::Fr>>::new();
    let one = E::Fr::one();

    points.push((
        E::Fr::from_str(
            "47847771272602875687997868466650874407263908316223685522183521003714784842376",
        )
        .unwrap(),
        E::Fr::from_str(
            "14866155869058627094034298869399931786023896160785945564212907054495032619276",
        )
        .unwrap(),
    ));
    points.push((
        E::Fr::from_str(
            "23161233924022868901612849355320019731199638537911088707556787060776867075186",
        )
        .unwrap(),
        E::Fr::from_str(
            "46827933816106251659874509206068992514697956295153175925290603211849263285943",
        )
        .unwrap(),
    ));
    points.push((
        E::Fr::from_str(
            "21363808388261502515395491234587106714641012878496416205209487567367794065894",
        )
        .unwrap(),
        E::Fr::from_str(
            "35142660575087949075353383974189325596183489114769964645075603269317744401507",
        )
        .unwrap(),
    ));
    points.push((
        E::Fr::from_str(
            "48251804265475671293065183223958159558134840367204970209791288593670022317146",
        )
        .unwrap(),
        E::Fr::from_str(
            "39492112716472193454928048607659273702179031506049462277700522043303788873919",
        )
        .unwrap(),
    ));
    points.push((
        E::Fr::from_str(
            "26076779737997428048634366966120809315559597005242388987585832521797042997837",
        )
        .unwrap(),
        E::Fr::from_str(
            "2916200718278883184735760742052487175592570929008292238193865643072375227389",
        )
        .unwrap(),
    ));
    points.push((
        E::Fr::from_str(
            "6391827799982489600548224857168349263868938761394485351819740320403055736778",
        )
        .unwrap(),
        E::Fr::from_str(
            "26714606321943866209898052587479168369119695309696311252068260485776094410355",
        )
        .unwrap(),
    ));
    points.push((
        E::Fr::from_str(
            "34225834605492133647358975329540922898558190785910349822925459742326697718965",
        )
        .unwrap(),
        E::Fr::from_str(
            "42503065208497349411091392685178794164009360876034587048702740318812028372175",
        )
        .unwrap(),
    ));
    points.push((
        E::Fr::from_str(
            "39706901109420478047209734657640449984347408718517226120651505259450485889935",
        )
        .unwrap(),
        E::Fr::from_str(
            "44842351859583855521445972897388346257004580582454107427806918461747670509399",
        )
        .unwrap(),
    ));
    points.push((
        E::Fr::from_str(
            "28360026567573852013315702401149784452531421169317971653481741133982080381509",
        )
        .unwrap(),
        E::Fr::from_str(
            "34586051224595854378884048103686100857425100914523816028360306191122507857625",
        )
        .unwrap(),
    ));
    points.push((
        E::Fr::from_str(
            "45719850001957217643735562111452029570487585222534789798311082643976688162166",
        )
        .unwrap(),
        E::Fr::from_str(
            "51398963553553644922019770691279615862813421731845531818251689044792926267778",
        )
        .unwrap(),
    ));

    // check whether the points are on the curve
    for i in 0..points.len() {
        let (x, y) = points[i];
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
            The point is on the curve, compute the witness and verify the circuit satisfiability for
            each point.

                Wire labels
                a=[y, x, yy]
                b=[y, x, dxx]
                c= [yy, xx, yy-xx-1]
        */

        let mut witness = Witness::<E::Fr>::create(3, rng);
        witness.gates[0] = CircuitGate::<E::Fr> { a: y, b: y, c: yy };
        witness.gates[1] = CircuitGate::<E::Fr> { a: x, b: x, c: xx };
        witness.gates[2] = CircuitGate::<E::Fr> {
            a: yy,
            b: dxx,
            c: yy_xx_1,
        };

        // verify the circuit satisfiability by the computed witness
        assert_eq!(cs.verify(None, &witness), true);

        // add the witness to the batch
        witness_batch.push(witness);
    }

    // The computation circuit is satisfied by the witness array
    // Now let's create zk-proof batch of the statements

    let s = String::from(
        "In the blockchain setting this has to come from the block context"
    );
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
                Ok(_) => {}
            }
        }
    }
}

fn negative<E: Engine>(urs: &URS<E>, cs: &ConstraintSystem<E::Fr>, rng: &mut OsRng) {
    let d = E::Fr::from_str(
        "19257038036680949359750312669786877991949435402254120286184196891950884077233",
    )
    .unwrap();

    // We have the constraint system. Let's choose examples of satisfying witness for Jubjub
    // y^2-x^2=1+d*y^2*x^2
    let mut points = Vec::<(E::Fr, E::Fr)>::new();
    let mut witness_batch = Vec::<Witness<E::Fr>>::new();
    let one = E::Fr::one();

    // witness that does not satisfy the statement
    points.push((
        E::Fr::from_str(
            "45719850001957217643735562111452029570487585222534789798311082643976688162166",
        )
        .unwrap(),
        E::Fr::from_str(
            "51398963553553644922019770691279615862813421731845531818251689044792926267779",
        )
        .unwrap(),
    ));

    // check whether the points are on the curve
    for i in 0..points.len() {
        let (x, y) = points[i];
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
            the point is on the curve, compute the witness and verify the circuit satisfiability for each point
                Wire labels
                a=[y, x, yy]
                b=[y, x, dxx]
                c= [yy, xx, yy-xx-1]
        */

        let mut witness = Witness::<E::Fr>::create(3, rng);
        witness.gates[0] = CircuitGate::<E::Fr> { a: y, b: y, c: yy };
        witness.gates[1] = CircuitGate::<E::Fr> { a: x, b: x, c: xx };
        witness.gates[2] = CircuitGate::<E::Fr> {
            a: yy,
            b: dxx,
            c: yy_xx_1,
        };

        // verify the circuit satisfiability by the computed witness
        assert_ne!(cs.verify(None, &witness), true);

        // add the witness to the batch
        witness_batch.push(witness);
    }

    // The computation circuit is satisfied by the witness array
    // Now let's create zk-proof batch of the statements

    let s = String::from(
        "In the blockchain setting this has to come from the block context"
    );
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
                Err(_) => {}
                Ok(_) => {
                    panic!("Failure invalidating the zk-proof");
                }
            }
        }
    }
}
