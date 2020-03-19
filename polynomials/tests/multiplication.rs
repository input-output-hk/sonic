/*****************************************************************************************************************

This source file implements the univariate polynomial test suite driver.
The following tests are implemented:

1. Univariate polynomial multiplication test
    1. Generate two random univariate polynomials A & B
    2. For a random field element x
        a. evaliate A at x and B at x
        b. multiply evaluations to obtain z1
        c. muliply polynomials A & B
        a. evaliate A*B at x
        b. record result of the above as z2
    3. Compare results z1 & z2

*****************************************************************************************************************/

use pairing::{bls12_381::Bls12, Engine, Field};
use polynomials::univariate::Univariate;
use rand::OsRng;
use rand::Rng;

#[test]
fn univariate_mul_test() {
    test::<Bls12>();
}

fn test<E: Engine>() {
    let mut rng = OsRng::new().unwrap();
    let depth = 1000;
    for _ in 0..10 {
        // generate sample random polynomials over the scalar field
        let a = Univariate::<E::Fr>::random(
            rng.gen_range::<usize>(1, depth),
            rng.gen_range::<usize>(0, depth),
            &mut rng,
        );
        let b = Univariate::<E::Fr>::random(
            rng.gen_range::<usize>(1, depth),
            rng.gen_range::<usize>(0, depth),
            &mut rng,
        );

        // we have the polynomials, evaluate them at a random scalar field element
        for _ in 0..10 {
            let x = Univariate::rand(&mut rng);
            let ax = a.evaluate(x).unwrap();
            let bx = b.evaluate(x).unwrap();
            let mut axbx = ax;
            axbx.mul_assign(&bx);
            let ab = a.mul(&b);
            let abx = ab.evaluate(x).unwrap();
            assert_eq!(abx, axbx);
        }
    }
}
