/*****************************************************************************************************************

This source file implements Sonic computation witness primitive.

Sonic witness consists of value assignements to the circuit wires that provide input and carry output values
to/from the multiplicative gates of the circuit. Thus assigned value witness is defined as three vectors of wire
label value assignements:

Left input A
Right input B
Output C

*****************************************************************************************************************/

pub use super::gate::CircuitGate;
use pairing::{Field, PrimeField};
use polynomials::univariate::Univariate;
use rand::OsRng;

#[derive(Clone)]
pub struct Witness<F: Field> {
    pub gates: Vec<CircuitGate<F>>, // circuit gate array
    blinders: (F, F, F, F),
}

impl<F: PrimeField> Witness<F> {
    // This function creates zero-instance witness of given depth
    pub fn create(n: usize, rng: &mut OsRng) -> Self {
        Self {
            gates: vec![CircuitGate::<F>::create(); n],
            blinders: (
                Univariate::<F>::rand(rng),
                Univariate::<F>::rand(rng),
                Univariate::<F>::rand(rng),
                Univariate::<F>::rand(rng),
            ),
        }
    }

    // This function constructs r polynomial from the witness
    pub fn compute(&self, y: F) -> Univariate<F> {
        let depth = self.gates.len();
        let mut rx = Univariate::<F>::create(2 * depth + 5, depth + 1);

        // adjust rx with blinders
        rx.neg[2 * depth + 1] = self.blinders.0;
        rx.neg[2 * depth + 2] = self.blinders.0;
        rx.neg[2 * depth + 3] = self.blinders.0;
        rx.neg[2 * depth + 4] = self.blinders.0;

        if y == F::one() {
            for i in 0..depth {
                rx.pos[i + 1] = self.gates[i].a;
                rx.neg[i + 1] = self.gates[i].b;
                rx.neg[i + depth + 1] = self.gates[i].c;
            }
        } else {
            let yinv = y.inverse().unwrap();
            let mut yaccinv = F::one();
            let mut yacc = F::one();
            for i in 0..depth {
                yacc.mul_assign(&y);
                rx.pos[i + 1] = self.gates[i].a;
                rx.pos[i + 1].mul_assign(&yacc);
                yaccinv.mul_assign(&yinv);
                rx.neg[i + 1] = self.gates[i].b;
                rx.neg[i + 1].mul_assign(&yaccinv);
            }
            for i in 0..depth {
                yaccinv.mul_assign(&yinv);
                rx.neg[i + depth + 1] = self.gates[i].c;
                rx.neg[i + depth + 1].mul_assign(&yaccinv);
            }
            for i in 0..4 {
                yaccinv.mul_assign(&yinv);
                rx.neg[2 * depth + 1 + i].mul_assign(&yaccinv);
            }
        }
        rx
    }
}
