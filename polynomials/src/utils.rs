/*****************************************************************************************************************

This source file implements miscellaneous utilities.

*****************************************************************************************************************/

pub use super::univariate::Univariate;
use pairing::PrimeField;
use rand::{OsRng, Rand};

impl<F: PrimeField> Univariate<F> {
    pub fn rand(rng: &mut OsRng) -> F {
        loop {
            if let Ok(y) = F::from_repr(F::Repr::rand(rng)) {
                return y;
            }
        }
    }

    // This function creates a zero instance of a polynomial of given dimensions
    pub fn random(n: usize, p: usize, rng: &mut OsRng) -> Self {
        let mut plnm = Self::create(n, p);
        for x in plnm.neg.iter_mut() {
            *x = Self::rand(rng);
        }
        for x in plnm.pos.iter_mut() {
            *x = Self::rand(rng);
        }
        plnm
    }
}
