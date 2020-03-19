/*****************************************************************************************************************

This source file implements the polynomial commitment unit test suite driver.
The following tests are implemented:

1. Polynomial commiment test
    1. Generate URS instance of sufficient depth
    2. Generate a random polynomials vector over the base field that fits into the URS depth.
       The polynomial coefficients are random base field elements.
    3. Commit to the polynomials against the URS instance
    4. Evaluate the polynomials at a given randomly generated base field elements
    5. Open the polynomials commitment at the given random base field element producing the opening proof
    6. Verify the commitment opening proofs against the:
        a. the URS instance
        b. Polynomial evaluations at the given base field element
        c. The given base field elements
        d. Commitment opening proofs

*****************************************************************************************************************/

use commitment::urs::URS;
use pairing::{bls12_381::Bls12, Engine, Field};
use polynomials::univariate::Univariate;
use rand::OsRng;

#[test]
fn single_commitment_test() {
    test::<Bls12>();
}

fn test<E: Engine>() {
    let mut rng = OsRng::new().unwrap();
    let depth = 50;

    // generate sample URS
    let urs = URS::<E>::create(
        depth,
        vec![depth / 3 - 3],
        Univariate::<E::Fr>::rand(&mut rng),
        Univariate::<E::Fr>::rand(&mut rng),
    );

    // generate sample random vector of polynomials over the base field, commit and evaluate them
    let mut plnms: Vec<(E::Fr, E::Fr, Vec<(E::G1Affine, E::Fr, usize)>, E::G1Affine)> = Vec::new();
    for _ in 0..10 {
        let plnm = Univariate::<E::Fr> {
            pos: (0..depth / 3 - 3)
                .map(|_| -> E::Fr { Univariate::<E::Fr>::rand(&mut rng) })
                .collect(),
            neg: (0..depth / 3 - 7)
                .map(|_| -> E::Fr { Univariate::<E::Fr>::rand(&mut rng) })
                .collect(),
        };
        let y = Univariate::<E::Fr>::rand(&mut rng);
        let comm = urs.commit(&plnm, plnm.pos.len());
        // Open and verify the polynomial commitments
        match plnm.evaluate(y) {
            None => {
                panic!("This error should not happen");
            }
            Some(eval) => match urs.open(&plnm, y) {
                None => {
                    panic!("This error should not happen");
                }
                Some(prf) => {
                    plnms.push((y, E::Fr::one(), vec![(comm, eval, depth / 3 - 3)], prf));
                }
            },
        }
    }
    assert_eq!(true, urs.verify(&vec![plnms; 1], &mut rng));
}
