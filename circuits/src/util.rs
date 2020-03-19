pub use super::constraint_system::ConstraintSystem;
pub use super::witness::Witness;
use pairing::{Engine, Field};

pub fn compute_sparseness<E: Engine>(
    cs: &mut ConstraintSystem<E::Fr>,
    witness: &mut Witness<E::Fr>,
) {
    let mut count = 0;
    let mut total = 0;
    for wt in witness.gates.iter() {
        if wt.a.is_zero() {
            count = count + 1;
        }
        if wt.b.is_zero() {
            count = count + 1;
        }
        if wt.c.is_zero() {
            count = count + 1;
        }
        total = total + 3
    }
    println!(
        "total: {}, zeros:: {}, ratio: {}",
        total,
        count,
        (count as f64) / (total as f64)
    );

    let mut count = 0;
    let mut total = 0;
    for i in 0..cs.a.rows() {
        for j in 0..cs.a.cols() {
            match cs.a.get(i, j) {
                None => count = count + 1,
                Some(_) => {}
            }
        }
    }
    for i in 0..cs.b.rows() {
        for j in 0..cs.b.cols() {
            match cs.b.get(i, j) {
                None => count = count + 1,
                Some(_) => {}
            }
        }
    }
    for i in 0..cs.c.rows() {
        for j in 0..cs.c.cols() {
            match cs.c.get(i, j) {
                None => count = count + 1,
                Some(_) => {}
            }
        }
    }
    total = total + 3;

    println!(
        "total: {}, zeros:: {}, ratio: {}",
        total,
        count,
        (count as f64) / (total as f64)
    );
}
