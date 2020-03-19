/*****************************************************************************************************************

This source file implements the polynomial commitment batch primitive. The primitive provides the following zero-
knowledge protocol:

1. Commit to the batch of vectors of polynomials against the URS instance
2. Evaluate the vector of polynomials at the given base field element
3. Open the polynomial commitment batch at the given random base field element producing the opening proof
   with the masking base field element
4. Verify the commitment opening proof against the following;
     a. the URS instance
     b. Polynomial evaluations at the given base field element
     c. The given base field element
     d. The given masking base field element
     e. Commitment opening proof

*****************************************************************************************************************/

pub use super::urs::URS;
use pairing::{CurveAffine, CurveProjective, Engine, Field, PrimeField, PrimeFieldRepr};
use polynomials::univariate::Univariate;
use rand::OsRng;
use rayon::prelude::*;

impl<E: Engine> URS<E> {
    // This function commits the polynomial against URS instance
    //     plnm: polynomial to commit
    //     max: maximal degree of the polynomial
    //     RETURN: commitment group element
    pub fn commit(&self, plnm: &Univariate<E::Fr>, max: usize) -> E::G1Affine {
        let d = self.gnax.len();
        let mut exp: Vec<(E::G1Affine, E::Fr)> = vec![];

        for i in 0..plnm.pos.len() {
            if plnm.pos[i].is_zero() {
                continue;
            }
            if i + d >= max {
                exp.push((self.gpax[i + d - max], plnm.pos[i]))
            } else {
                exp.push((self.gnax[max - i - d], plnm.pos[i]))
            }
        }
        for i in 1..plnm.neg.len() {
            if plnm.neg[i].is_zero() {
                continue;
            }
            if i + max >= d {
                exp.push((self.gnax[i + max - d], plnm.neg[i]))
            } else {
                exp.push((self.gpax[d - i - max], plnm.neg[i]))
            }
        }
        Self::multiexp(&exp)
    }

    // This function exponentiates the polynomial against URS instance
    //     plnm: polynomial to exponentiate
    //     RETURN: commitment group element
    pub fn exponentiate(&self, plnm: &Univariate<E::Fr>) -> Option<E::G1Affine> {
        if plnm.pos.len() > self.gp1x.len() || plnm.neg.len() > self.gn1x.len() {
            return None;
        }
        let mut exp: Vec<(E::G1Affine, E::Fr)> = vec![];

        for (x, y) in plnm.pos.iter().zip(self.gp1x.iter()) {
            if x.is_zero() {
                continue;
            }
            exp.push((*y, *x));
        }
        for (x, y) in plnm.neg.iter().skip(1).zip(self.gn1x.iter().skip(1)) {
            if x.is_zero() {
                continue;
            }
            exp.push((*y, *x));
        }
        Some(Self::multiexp(&exp))
    }

    // This function opens the polynomial commitment
    //     elm: base field element to open the commitment at
    //     plnm: commited polynomial
    //     RETURN: commitment opening proof
    pub fn open(&self, plnm: &Univariate<E::Fr>, elm: E::Fr) -> Option<E::G1Affine> {
        // do polynomial division (F(x)-F(elm))/(x-elm)
        match plnm.divide(elm) {
            None => None,
            Some(div) => self.exponentiate(&div),
        }
    }

    // This function computes the polynomial commitment batch
    //     plnms: batch of polynomials to commit
    //     urs: universal reference string
    //     RETURN: evaluation field element result
    pub fn commit_batch(&self, plnms: &Vec<(Univariate<E::Fr>, usize)>) -> Vec<E::G1Affine> {
        let mut commitment = vec![E::G1Affine::zero(); plnms.len()];
        for (x, y) in commitment.iter_mut().zip(plnms.iter()) {
            *x = self.commit(&y.0, y.1);
        }
        commitment
    }

    // This function opens the polynomial commitment batch
    //     plnms: batch of commited polynomials
    //     mask: base field element masking value
    //     elm: base field element to open the commitment at
    //     RETURN: commitment opening proof
    pub fn open_batch(
        &self,
        plnms: &Vec<Univariate<E::Fr>>,
        mask: E::Fr,
        elm: E::Fr,
    ) -> Option<E::G1Affine> {
        let mut acc = Univariate::<E::Fr>::create(0, 0);
        let mut scale = mask;

        for x in plnms.iter() {
            acc = acc.add_alloc(&x.mul_assign(scale));
            scale.mul_assign(&mask);
        }
        match acc.divide(elm) {
            None => None,
            Some(div) => self.exponentiate(&div),
        }
    }

    // This function updates the polynomial commitment opening batch with another opening proof
    //     batch: polynomial commitment opening batch to update
    //     proof: polynomial commitment opening proof to update with
    //     mask: base field element masking value
    //     index: update index
    //     RETURN: updated commitment opening batch proof
    pub fn update_batch(
        batch: E::G1Affine,
        proof: E::G1Affine,
        mut mask: E::Fr,
        index: usize,
    ) -> E::G1Affine {
        mask = mask.pow(&[index as u64]);
        let mut projt = batch.into_projective();
        projt.add_assign(&proof.mul(mask));
        projt.into_affine()
    }

    // This function verifies the batch polynomial commitment proofs of vectors of polynomials
    //     base field element to open the commitment at
    //     base field element masking value
    //     polynomial commitment batch of
    //         commitment value
    //         polynomial evaluation
    //         max positive powers size of the polynomial
    //     polynomial commitment opening proof
    //     RETURN: verification status
    pub fn verify(
        &self,
        batch: &Vec<Vec<(E::Fr, E::Fr, Vec<(E::G1Affine, E::Fr, usize)>, E::G1Affine)>>,
        rng: &mut OsRng,
    ) -> bool {
        let d = self.gnax.len();
        let mut open: Vec<(E::G1Affine, E::Fr)> = vec![];
        let mut openy: Vec<(E::G1Affine, E::Fr)> = vec![];
        let mut table = vec![];

        for prf in batch.iter() {
            let mut pcomm: Vec<Vec<(E::G1Affine, E::Fr)>> = vec![vec![]; prf[0].2.len()];
            let mut eval = E::Fr::zero();

            for x in prf.iter() {
                let rnd = Univariate::<E::Fr>::rand(rng);
                open.push((x.3, rnd));
                let mut ry = rnd;
                ry.mul_assign(&x.0);
                ry.negate();
                openy.push((x.3, ry));
                let mut scale = x.1;
                let mut v = E::Fr::zero();

                for (z, y) in x.2.iter().zip(pcomm.iter_mut()) {
                    let mut vi = z.1;
                    vi.mul_assign(&scale);
                    v.add_assign(&vi);
                    let mut vj = rnd;
                    vj.mul_assign(&scale);
                    y.push((z.0, vj));
                    scale.mul_assign(&x.1);
                }
                v.mul_assign(&rnd);
                eval.add_assign(&v);
            }
            openy.push((self.gp1x[0], eval));
            for (z, y) in prf[0].2.iter().zip(pcomm.iter_mut()) {
                if !self.hn1x.contains_key(&(d - z.2)) {
                    return false;
                }
                table.push((
                    Self::multiexp(&y).prepare(),
                    ({
                        let mut g = self.hn1x[&(d - z.2)];
                        g.negate();
                        g
                    })
                    .prepare(),
                ));
            }
        }
        table.push((Self::multiexp(&open).prepare(), self.hpax1.prepare()));
        table.push((Self::multiexp(&openy).prepare(), self.hpax0.prepare()));
        let x: Vec<(
            &<E::G1Affine as CurveAffine>::Prepared,
            &<E::G2Affine as CurveAffine>::Prepared,
        )> = table.iter().map(|x| (&x.0, &x.1)).collect();
        E::final_exponentiation(&E::miller_loop(&x)).unwrap() == E::Fqk::one()
    }

    // This function multipoint exponentiates the array of group and scalar element tuples
    //     this implementation of the multiexponentiation's Pippenger algorithm
    //     is adapted from that of zexe algebra crate
    //     RETURN: multipoint exponentiaton result
    pub fn multiexp<G: CurveAffine>(elm: &Vec<(G, G::Scalar)>) -> G {
        let bases = elm.iter().map(|p| p.0).collect::<Vec<_>>();
        let scalars = elm.iter().map(|p| p.1.into_repr()).collect::<Vec<_>>();

        let c = if scalars.len() < 32 {
            3
        } else {
            (2.0 / 3.0 * (f64::from(scalars.len() as u32)).log2() + 2.0).ceil() as usize
        };

        let num_bits = <G::Engine as Engine>::Fr::NUM_BITS as usize;
        let fr_one = G::Scalar::one().into_repr();

        let zero = G::zero().into_projective();
        let window_starts: Vec<_> = (0..num_bits).step_by(c).collect();

        let window_sums: Vec<_> = window_starts
            .into_par_iter()
            .map(|w_start| {
                let mut res = zero;
                let mut buckets = vec![zero; (1 << c) - 1];
                scalars
                    .iter()
                    .zip(bases.iter())
                    .filter(|(s, _)| !s.is_zero())
                    .for_each(|(&scalar, base)| {
                        if scalar == fr_one {
                            if w_start == 0 {
                                res.add_assign_mixed(&base);
                            }
                        } else {
                            let mut scalar = scalar;
                            scalar.shr(w_start as u32);
                            let scalar = scalar.as_ref()[0] % (1 << c);
                            if scalar != 0 {
                                buckets[(scalar - 1) as usize].add_assign_mixed(&base);
                            }
                        }
                    });
                G::Projective::batch_normalization(&mut buckets);

                let mut running_sum = G::Projective::zero();
                for b in buckets.into_iter().map(|g| g.into_affine()).rev() {
                    running_sum.add_assign_mixed(&b);
                    res.add_assign(&running_sum);
                }
                res
            })
            .collect();

        let lowest = window_sums.first().unwrap();
        let mut sums = window_sums[1..]
            .iter()
            .rev()
            .fold(zero, |mut total, sum_i| {
                total.add_assign(&sum_i);
                for _ in 0..c {
                    total.double()
                }
                total
            });
        sums.add_assign(&lowest);
        sums.into_affine()
    }
}
