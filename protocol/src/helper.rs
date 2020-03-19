/********************************************************************************************

This source file implements helper's zk-proof primitives.

This proof is constructed by helper after the successfull verification of the ProverProof. It
is verified by the verifier as part of the verification of the NP-statement Sonic zk-proof.
This is one of the two constituent parts of the NP-statement Sonic zk-proof, the other being
the ProverProof.

*********************************************************************************************/

pub use super::batch::{ProofError, ProverProof, RandomOracleArgument};
use circuits::constraint_system::ConstraintSystem;
use commitment::urs::URS;
use pairing::Engine;
use polynomials::univariate::Univariate;
use rand::OsRng;
use sprs::CsVec;

#[derive(Clone, Copy)]
pub struct HelperProof<E: Engine> {
    // Commitment to univariate polynomial s(X, y)
    pub sxy_comm: E::G1Affine,
    // s(X, y) evaluation at x
    pub sxy_x_evl: E::Fr,
    // Commitment sxy_comm to s(X, y) opening at u
    pub sxy_u_prf: E::G1Affine,
    pub sxy_u_evl: E::Fr,
    // Proof of commitment sux_comm to s(u, X) opening at y
    pub sux_y_prf: E::G1Affine,
}

impl<E: Engine> HelperProof<E> {
    // This function constructs helper's zk-proof from the constraint system and prover's proof against URS instance
    //     prover: prover's proof
    //     cs: constraint system
    //     k: optional public params as vector K update
    //     sux: batch proof polynomial reference
    //     urs: universal reference string
    //     u: random oracle from the batch proof
    //     verify: flag indicating whether to verify the prover's proof (if verified in batch)
    //     RETURN: helper's zk-proof
    pub fn create(
        prover: &mut ProverProof<E>,
        cs: &ConstraintSystem<E::Fr>,
        k: Option<CsVec<E::Fr>>,
        sux: &Univariate<E::Fr>,
        urs: &URS<E>,
        verify: bool,
        u: E::Fr,
    ) -> Result<Self, ProofError> {
        let mut rng = OsRng::new().unwrap();
        // the prover's transcript of the random oracle non-interactive argument
        let (x, y, _, mask) = prover.oracles(cs, &k);

        // compute s(X, y) polynomial
        let rslt = cs.evaluate_s(y, false);
        if rslt.is_none() {
            return Err(ProofError::SXyxEvalComputation);
        }
        let sxy = rslt.unwrap();

        // eveluate s(X, Y) at (x, y)
        let rslt = sxy.evaluate(x);
        if rslt.is_none() {
            return Err(ProofError::SXyxEvalComputation);
        }
        let sxy_x_evl = rslt.unwrap();

        // vrify the prover's proof if batch verification was not successfull
        if verify && !prover.verify(&sxy_x_evl, cs, k, urs, &mut rng) {
            return Err(ProofError::ProverVerification);
        }

        // commit to univariate polynomial s(X, y)
        let sxy_comm = urs.commit(&sxy, cs.a.shape().1 * 2 + 1);

        // helper opens the polynomial s(X, y) commitment at x by updating prover's batch_x_prf
        let rslt = urs.open(&sxy, x);
        if rslt.is_none() {
            return Err(ProofError::SXyxPrfComputation);
        }
        prover.batch_x_prf = URS::<E>::update_batch(prover.batch_x_prf, rslt.unwrap(), mask, 3);

        // helper opens the polynomial s(X, y) commitment at u
        let rslt = sxy.evaluate(u);
        if rslt.is_none() {
            return Err(ProofError::SXyuEvalComputation);
        }
        let sxy_u_evl = rslt.unwrap();
        let rslt = urs.open(&sxy, u);
        if rslt.is_none() {
            return Err(ProofError::SXyuPrfComputation);
        }
        let sxy_u_prf = rslt.unwrap();

        // helper opens the polynomial s(u, X) commitment at y
        let rslt = urs.open(&sux, y);
        if rslt.is_none() {
            return Err(ProofError::SuXyPrfComputation);
        }
        let sux_y_prf = rslt.unwrap();

        Ok(HelperProof {
            sxy_comm: sxy_comm,
            sxy_x_evl: sxy_x_evl,
            sxy_u_prf: sxy_u_prf,
            sxy_u_evl: sxy_u_evl,
            sux_y_prf: sux_y_prf,
        })
    }
}
