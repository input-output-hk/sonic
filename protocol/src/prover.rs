/********************************************************************************************

This source file implements prover's zk-proof primitives.

This proof is constructed by prover. It is verified by both the helper and the verifier as
part of the computation of the helper's proof as well as the verification of the NP-statement
Sonic zk-proof. This is one of the two constituent parts of the NP-statement Sonic zk-proof,
the other being the HelperProof.

*********************************************************************************************/

pub use super::rndoracle::{ProofError, RandomOracleArgument};
use circuits::constraint_system::{ConstraintSystem, Witness};
use commitment::urs::URS;
use merlin::Transcript;
use pairing::{Engine, Field};
use polynomials::univariate::Univariate;
use rayon::prelude::*;
use rand::OsRng;
use sprs::CsVec;

#[derive(Clone, Copy)]
pub struct ProverProof<E: Engine> {
    // Commitment to univariate polynomial r(X, 1)
    pub rx1_comm: E::G1Affine,
    // Commitment to univariate polynomial t(X, y)
    pub txy_comm: E::G1Affine,
    // Commitment to rx1, txy & sxy to r(X, 1) opening at x batched proof
    pub batch_x_prf: E::G1Affine,
    // rx1 evaluation at x
    pub rx1_x_evl: E::Fr,
    // Commitment rx1_comm to r(X, 1) opening at xy
    pub rx1_xy_prf: E::G1Affine,
    pub rx1_xy_evl: E::Fr,
}

impl<E: Engine> ProverProof<E> {
    // This function constructs prover's zk-proof from the witness & the constraint system against URS instance
    //     witness: computation witness
    //     cs: constraint system
    //     k: optional public params as vector K update
    //     urs: universal reference string
    //     RETURN: prover's zk-proof
    pub fn create(
        witness: &Witness<E::Fr>,
        cs: &ConstraintSystem<E::Fr>,
        k: Option<CsVec<E::Fr>>,
        urs: &URS<E>,
    ) -> Result<Self, ProofError> {
        // the transcript of the random oracle non-interactive argument
        let mut argument = Self::fiatshamir(cs, &k);

        // compute r(X, 1) polynomial
        let rx1 = witness.compute(E::Fr::one());

        // commit to univariate polynomial r(X, 1)
        let rx1_comm = urs.commit(&rx1, cs.a.shape().1 + 1);

        // add r(X, 1) commitment to the random oracle context
        argument.commit_point(&rx1_comm);

        // query random scalar challenge from verifier
        let y: E::Fr = argument.challenge();

        // compute t(X, y) polynomial
        let rslt = Self::t(witness, cs, k, rx1.clone(), y);
        if rslt.is_none() {
            return Err(ProofError::TXyxEvalComputation);
        }
        let txy = rslt.unwrap();

        // commit to univariate polynomial t(X, y)
        let txy_comm = urs.commit(&txy, urs.gnax.len());

        // add t(X, y) commitment to the random oracle context
        argument.commit_point(&txy_comm);

        // query random scalar challenge from verifier
        let x: E::Fr = argument.challenge();

        let mut xy = x;
        xy.mul_assign(&y);

        // prover opens the polynomial r(X, 1) commitment at xy
        let rslt = rx1.evaluate(xy);
        if rslt.is_none() {
            return Err(ProofError::RX1xyEvalComputation);
        }
        let rx1_xy_evl = rslt.unwrap();
        let rslt = urs.open(&rx1, xy);
        if rslt.is_none() {
            return Err(ProofError::RX1xyPrfComputation);
        }
        let rx1_xy_prf = rslt.unwrap();

        // add r(X, 1) opening proof to the random oracle context
        argument.commit_point(&rx1_xy_prf);

        // query random scalar mask challenge from verifier
        let mask: E::Fr = argument.challenge();

        // prover supplies the polynomial r(X, 1) evaluation at x
        let rslt = rx1.evaluate(x);
        if rslt.is_none() {
            return Err(ProofError::RX1xEvalComputation);
        }
        let rx1_x_evl = rslt.unwrap();

        // prover opens the polynomial t(X, y) & r(X, 1) commitments at x
        let rslt = urs.open_batch(&vec![txy, rx1], mask, x);
        if rslt.is_none() {
            return Err(ProofError::RX1xPrfComputation);
        }
        let batch_x_prf = rslt.unwrap();

        Ok(ProverProof {
            rx1_comm: rx1_comm,
            txy_comm: txy_comm,
            batch_x_prf: batch_x_prf,
            rx1_x_evl: rx1_x_evl,
            rx1_xy_prf: rx1_xy_prf,
            rx1_xy_evl: rx1_xy_evl,
        })
    }

    // This function constructs prover's zk-proofs in parallel from the
    // witness vector & the constraint system against URS instance
    //     witness: computation witness array with
    //          optional public params as vector K update
    //     cs: constraint system
    //     urs: universal reference string
    //     RETURN: prover's zk-proof array
    pub fn create_parallel
    (
        witness: &Vec<(Witness<E::Fr>, Option<CsVec<E::Fr>>)>,
        cs: &ConstraintSystem<E::Fr>,
        urs: &URS<E>,
    ) -> Result<Vec<Self>, ProofError>
    {
        witness.par_iter().map
        (
            |witness| ProverProof::<E>::create
            (
                &witness.0,
                cs,
                witness.1.clone(),
                urs,
            )
        ).collect::<Result<Vec<_>, _>>()
    }

    // This function verifies the prover's zk-proof
    //     sxy: evaluation of s(X, Y) polynomial at (x, y). Helper, upon verification,
    //     computes the value himself. Verifier, upon verification, provides this evaluation as
    //     computed by the helper
    //     cs: constraint system
    //     k: optional public params as vector K update
    //     urs: universal reference string
    //     RETURN: verification status
    pub fn verify(
        &self,
        sxy: &E::Fr,
        cs: &ConstraintSystem<E::Fr>,
        k: Option<CsVec<E::Fr>>,
        urs: &URS<E>,
        rng: &mut OsRng,
    ) -> bool {
        // query random oracle values from verifier
        let (x, y, xy, mask) = self.oracles(cs, &k);

        // evaluate k(Y) at y
        let ky = match k
        {
            Some(k) =>
            {
                let mut rslt = E::Fr::zero();
                for x in k.iter() {
                    let mut monom = *x.1;
                    monom.mul_assign(&y.pow(&[(x.0 + cs.a.shape().1 + 1) as u64]));
                    rslt.add_assign(&monom);
                }
                rslt
            }
            None => {cs.evaluate_k(k, y)}
        };

        // compute the evaluation of polynomial t(X, Y) at the point (x, y)
        let mut txy = self.rx1_xy_evl;
        txy.add_assign(&sxy);
        txy.mul_assign(&self.rx1_x_evl);
        txy.sub_assign(&ky);

        // verify the proof rx1_xy_prf against the commitment rx1_comm and evaluation rx1_xy_evl
        if urs.verify(
            &vec![
                vec![(
                    xy,
                    E::Fr::one(),
                    vec![(self.rx1_comm, self.rx1_xy_evl, cs.a.shape().1 + 1)],
                    self.rx1_xy_prf,
                )],
                vec![(
                    x,
                    mask,
                    vec![
                        (self.txy_comm, txy, urs.gnax.len()),
                        (self.rx1_comm, self.rx1_x_evl, cs.a.shape().1 + 1),
                    ],
                    self.batch_x_prf,
                )],
            ],
            rng,
        ) == false
        {
            return false;
        }
        true
    }

    // This function evaluation of t(X, Y) polynomial at (x, y)
    //     evaluations:
    //         ky: k(Y) polynomial evaluatoiion at y
    //         sxy: s(X, Y) polynomial evaluatoiion at (x, y)
    //     RETURN: prepared verification context:
    //         txy: t(X, Y) evaluation at (x, y)
    pub fn txy(&self, evaluations: (Option<E::Fr>, Option<E::Fr>)) -> Result<E::Fr, ProofError> {
        let (ky, sxy) = evaluations;
        match (ky, sxy) {
            (Some(ky), Some(sxy)) => {
                // compute the evaluation of polynomial t(X, Y) at the point (x, y)
                let mut txy = self.rx1_xy_evl;
                txy.add_assign(&sxy);
                txy.mul_assign(&self.rx1_x_evl);
                txy.sub_assign(&ky);
                Ok(txy)
            }
            (_, _) => return Err(ProofError::TXyxEvalComputation),
        }
    }

    // This function queries random oracle values from verifier
    pub fn fiatshamir(cs: &ConstraintSystem<E::Fr>, k: &Option<CsVec<E::Fr>>) -> Transcript {
        // the transcript of the random oracle non-interactive argument
        let mut argument = Transcript::new(&[]);
        // add public assignments into the argument
        match k
        {
            Some(k) => {for value in k.data().iter() {argument.commit_scalar(value)}}
            None => {for value in cs.k.data().iter() {argument.commit_scalar(value)}}
        }
        argument
    }

    // This function queries random oracle values from verifier
    pub fn oracles(&self, cs: &ConstraintSystem<E::Fr>, k: &Option<CsVec<E::Fr>>) -> (E::Fr, E::Fr, E::Fr, E::Fr) {
        // the transcript of the random oracle non-interactive argument
        let mut argument = Self::fiatshamir(cs, &k);
        // add r(X, 1) commitment to the random oracle context
        argument.commit_point(&self.rx1_comm);
        // query random scalar challenge from verifier
        let y: E::Fr = argument.challenge();
        // add t(X, y) commitment to the random oracle context
        argument.commit_point(&self.txy_comm);
        // query random scalar challenge from verifier
        let x: E::Fr = argument.challenge();
        // add r(X, 1) opening proof to the random oracle context
        argument.commit_point(&self.rx1_xy_prf);
        // query random scalar mask challenge from verifier
        let mask: E::Fr = argument.challenge();
        let mut xy = x;
        xy.mul_assign(&y);
        (x, y, xy, mask)
    }

    // This function constructs t polynomial from the witness & the constraint system
    //     witness: computation witness
    //     cs: constraint system
    //     k: optional public params as vector K update
    //     RETURN: s polynomial
    pub fn t(
        witness: &Witness<E::Fr>,
        cs: &ConstraintSystem<E::Fr>,
        k: Option<CsVec<E::Fr>>,
        rx1: Univariate<E::Fr>,
        y: E::Fr,
    ) -> Option<Univariate<E::Fr>> {
        let _shape = cs.a.shape();

        // compute r(X, y) polynomial
        let mut rxy = witness.compute(y);
        // compute s(X, y) polynomial
        match cs.evaluate_s(y, false) {
            None => return None,
            Some(sxy) => rxy.add_assign(&sxy),
        }

        // multiply r1 & rx1 polynomials
        let mut t = rxy.mul(&rx1);

        // subtract k(Y) polynomial
        t.pos[0].sub_assign(&cs.evaluate_k(k, y));
        Some(t)
    }
}
