/*****************************************************************************************************************

This source file implements Sonic computation circuit gate primitive.

Sonic factors out the linear relations for the computation into the system of linear constraints. The
computation circuit, modulo the linear relations, consists of multiplicative gates that have two inputs
and one output:

Left input A
Right input B
Output C

*****************************************************************************************************************/

use pairing::Field;

#[derive(Clone)]
pub struct CircuitGate<F: Field> {
    pub a: F, // left input wire
    pub b: F, // right input wire
    pub c: F, // output wire
}

impl<F: Field> CircuitGate<F> {
    // This function creates zero-instance circuit gate
    pub fn create() -> Self {
        Self {
            a: F::zero(),
            b: F::zero(),
            c: F::zero(),
        }
    }
}
