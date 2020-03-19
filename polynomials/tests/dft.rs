/*****************************************************************************************************************

This source file implements the Fast Fourier Transform test.
The tests proceeds as follows:

1. generate random vector
2. compute its Discrete Fourier Transform
3. compute the reverse Discrete Fourier Transform of the transform
4. compare the computed RDFT with the original vector

*****************************************************************************************************************/

use pairing::{bls12_381::Bls12, Engine, Field, PrimeField};
use polynomials::univariate::Univariate;
use rand::Rng;

#[test]
fn dft_test() {
    test::<Bls12>();
}

fn test<E: Engine>() {
    let mut rng = rand::thread_rng();
    let mut rand = || -> E::Fr {
        loop {
            let rnd: u64 = rng.gen();
            let x: String = rnd.to_string();
            if let Some(y) = E::Fr::from_str(&x) {
                return y;
            }
        }
    };

    let vec1: Vec<E::Fr> = (0..579).map(|_| -> E::Fr { rand() }).collect();
    let vec2 = Univariate::<E::Fr>::dft(vec1.clone(), None, false);
    let vec3 = Univariate::<E::Fr>::dft(vec2.clone(), None, true);
    let vec4 = Univariate::<E::Fr>::dft(vec3.clone(), None, false);
    let vec5 = Univariate::<E::Fr>::dft(vec4.clone(), None, true);

    fn eq<E: Engine>(mut a: E::Fr, b: E::Fr) -> bool {
        a.sub_assign(&b);
        a.is_zero()
    }
    assert_eq!(vec3.len(), vec5.len());
    assert_eq!(
        vec3.iter().zip(vec5.iter()).all(|(&a, &b)| eq::<E>(a, b)),
        true
    );
}
