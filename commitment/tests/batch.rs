/*****************************************************************************************************************

This source file implements the batched polynomial commitment unit test suite driver.
The following tests are implemented:

1. Batched polynomial commiment test
    1. Generate URS instance of sufficient depth
    2. Generate vector of vectors of random polynomials over the base field that fits into the URS depth.
       The polynomial coefficients are random base filed elements
    3. Commit to the polynomial vectors against the URS instance with masking/scaling value
    4. Evaluate the polynomials at a given randomly generated base field element
    5. Open the polynomial commitment vectors at the given random base field element producing the opening proof
    6. Verify the commitment vector opening proof against the:
        a. the URS instance
        b. Polynomial evaluations at the given base field element
        c. The given base field element
        d. Commitment opening proof

*****************************************************************************************************************/

use commitment::urs::URS;
use pairing::{bls12_381::Bls12, Engine};
use polynomials::univariate::Univariate;
use rand::OsRng;

#[test]
fn batch_commitment_test() {
    test::<Bls12>();
}

fn test<E: Engine>() {
    let mut rng = OsRng::new().unwrap();
    let depth = 50;

    // generate sample URS
    let urs = URS::<E>::create(
        depth,
        vec![depth / 3 - 3, depth / 3 - 4, depth / 3 - 5],
        Univariate::<E::Fr>::rand(&mut rng),
        Univariate::<E::Fr>::rand(&mut rng),
    );

    // generate random polynomials over the base field
    let mut block: Vec<(E::Fr, E::Fr, Vec<(E::G1Affine, E::Fr, usize)>, E::G1Affine)> = Vec::new();

    for _ in 0..7 {
        let elm = Univariate::<E::Fr>::rand(&mut rng);
        let mask = Univariate::<E::Fr>::rand(&mut rng);
        let mut plnms: Vec<Univariate<E::Fr>> = Vec::new();
        let mut max: Vec<usize> = Vec::new();
        let mut eval: Vec<E::Fr> = Vec::new();

        let mut plnm = Univariate::<E::Fr> {
            pos: (0..depth / 3 - 3)
                .map(|_| -> E::Fr { Univariate::<E::Fr>::rand(&mut rng) })
                .collect(),
            neg: (0..depth / 3 - 7)
                .map(|_| -> E::Fr { Univariate::<E::Fr>::rand(&mut rng) })
                .collect(),
        };

        max.push(plnm.pos.len());
        eval.push(plnm.evaluate(elm).unwrap());
        plnms.push(plnm);

        plnm = Univariate::<E::Fr> {
            pos: (0..depth / 3 - 4)
                .map(|_| -> E::Fr { Univariate::<E::Fr>::rand(&mut rng) })
                .collect(),
            neg: (0..depth / 3 - 9)
                .map(|_| -> E::Fr { Univariate::<E::Fr>::rand(&mut rng) })
                .collect(),
        };

        max.push(plnm.pos.len());
        eval.push(plnm.evaluate(elm).unwrap());
        plnms.push(plnm);

        plnm = Univariate::<E::Fr> {
            pos: (0..depth / 3 - 5)
                .map(|_| -> E::Fr { Univariate::<E::Fr>::rand(&mut rng) })
                .collect(),
            neg: (0..depth / 3 - 3)
                .map(|_| -> E::Fr { Univariate::<E::Fr>::rand(&mut rng) })
                .collect(),
        };

        max.push(plnm.pos.len());
        eval.push(plnm.evaluate(elm).unwrap());
        plnms.push(plnm);

        // Commit, open and verify the polynomial commitments
        let comm = urs.commit_batch(
            &plnms
                .clone()
                .into_iter()
                .zip(max.clone().into_iter())
                .collect(),
        );
        match urs.open_batch(&plnms, mask, elm) {
            None => {
                panic!("This error should not happen");
            }
            Some(prf) => {
                block.push((
                    elm,
                    mask,
                    comm.into_iter()
                        .zip(eval.into_iter())
                        .zip(max.into_iter())
                        .map(|((x, y), z)| (x, y, z))
                        .collect(),
                    prf,
                ));
            }
        }
    }
    assert_eq!(true, urs.verify(&vec![block; 1], &mut rng));
}
