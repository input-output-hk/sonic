/********************************************************************************************

This source file implements batch zk-proof primitives.

This primitive is the top-level aggregate of Sonic zk-proof format that provides means of
optimized batch verification of the individual constituent zk-proofs with a single evaluation
of a bivariate polynomial for all the proofs in the batch. It consists, besides the batch
proof group element values, the vector of individual zk-proofs that aggregate ProverProof
and HelperProof at the lower aggregation level.

*********************************************************************************************/

pub use super::helper::HelperProof;
pub use super::prover::ProverProof;
pub use super::rndoracle::{ProofError, RandomOracleArgument};
pub use super::zkproof::ZkProof;
use circuits::constraint_system::{ConstraintSystem};
use commitment::urs::URS;
use merlin::Transcript;
use pairing::{Engine, Field};
use rayon::prelude::*;
use rand::OsRng;
use sprs::CsVec;

pub struct BatchProof<E: Engine> {
    // Commitment to univariate polynomial s(u, X)
    pub sux_comm: E::G1Affine,
    // Commitment sux_comm to s(u, X) opening at v proof
    pub sux_v_prf: E::G1Affine,
    // batch of proof tuples with verification status
    pub batch: Vec<ZkProof<E>>,
}

impl<E: Engine> BatchProof<E> {
    // This function constructs helper's batch zk-proof from the
    // constraint system and prover's proofs against URS instance
    //     context: batch context for the random oracle argument
    //     prover: batch of prover's proofs with optional public parameter updates
    //     cs: constraint system
    //     urs: universal reference string
    //     RETURN: helper's batch zk-proof
    pub fn create(
        context: &Vec<u8>,
        provers: &Vec<(ProverProof<E>, Option<CsVec<E::Fr>>)>,
        cs: &ConstraintSystem<E::Fr>,
        urs: &URS<E>,
        rng: &mut OsRng,
    ) -> Result<Self, ProofError> {
        // the helper's transcript of the random oracle argument
        let mut argument = Transcript::new(&[]);
        // batch context for the random oracle argument
        argument.append_message(b"bytes", context);

        // query random scalar challenge from verifier
        let u: E::Fr = argument.challenge();

        // compute s(u, X) polynomial
        let rslt = cs.evaluate_s(u, true);
        if rslt.is_none() {
            return Err(ProofError::SuXvEvalComputation);
        }
        let sux = rslt.unwrap();

        // commit to univariate polynomial s(u, X)
        let sux_comm = urs.commit(&sux, cs.a.shape().1 + cs.a.shape().0 + 1);
        argument.commit_point(&sux_comm);

        // query random scalar challenge from verifier
        let v: E::Fr = argument.challenge();

        // helper opens the polynomial s(u, X) commitment at v
        let rslt = urs.open(&sux, v);
        if rslt.is_none() {
            return Err(ProofError::SuXvPrfComputation);
        }
        let sux_v_prf = rslt.unwrap();

        // retrieve random oracle values
        let mut oracles: Vec<(E::Fr, E::Fr, E::Fr, E::Fr)> = Vec::new();
        for proof in provers.iter() {
            oracles.push(proof.0.oracles(cs, &proof.1))
        }

        // assemble the prover's proofs into a proof vector over for verification over the batched EC pairings
        let mut vecver: bool = false;
        let mut prfrx1: Vec<(E::Fr, E::Fr, Vec<(E::G1Affine, E::Fr, usize)>, E::G1Affine)> =
            Vec::new();
        let mut prfbatch: Vec<(E::Fr, E::Fr, Vec<(E::G1Affine, E::Fr, usize)>, E::G1Affine)> =
            Vec::new();

        for (proof, oracle) in provers.iter().zip(oracles.iter()) {
            let rslt = cs.evaluate_s(oracle.0, true);
            if rslt.is_none() {
                return Err(ProofError::SXyxPrfComputation);
            }
            let sxy = rslt.unwrap();
            // evaluate k(Y) at oracle.1
            let ky = cs.evaluate_k(proof.1.clone(), oracle.1);
            match proof.0.txy((Some(ky), sxy.evaluate(oracle.1))) {
                Err(_) => {
                    vecver = true;
                    break;
                } // vector verification failed, will verify individual proofs
                Ok(txy) => {
                    prfrx1.push((
                        oracle.2,
                        E::Fr::one(),
                        vec![(proof.0.rx1_comm, proof.0.rx1_xy_evl, cs.a.shape().1 + 1)],
                        proof.0.rx1_xy_prf,
                    ));
                    prfbatch.push((
                        oracle.0,
                        oracle.3,
                        vec![
                            (proof.0.txy_comm, txy, urs.gnax.len()),
                            (proof.0.rx1_comm, proof.0.rx1_x_evl, cs.a.shape().1 + 1),
                        ],
                        proof.0.batch_x_prf,
                    ));
                }
            }
        }

        // verify the assembled vector proof rx1_xy_prf against the commitment rx1_comm and evaluations rx1_xy_evl
        // verify the assembled vector proof batch_x_prf against the commitments rx1_comm & txy_comm
        // and evaluations rx1_x_evl and the computed evaluations t(x, y) of the bivariate polynomial
        // t(X, Y) at the points (x, y)
        if urs.verify(&vec![prfrx1, prfbatch], rng) == false {
            vecver = true;
        }

        // assemble the individual proofs in parallel
        Ok
        (
            BatchProof
            {
                sux_comm,
                sux_v_prf,
                batch: provers.par_iter().map
                (
                    |prover|
                    {
                        let mut prover= prover.clone();
                        let helper = HelperProof::create(&mut prover.0, cs, prover.1, &sux, urs, vecver, u);
                        ZkProof { prover: prover.0, helper: helper}
                    }
                ).collect(),
            }
        )
    }

    // This function verifies the batch zk-proof
    //     context: batch context for the random oracle argument
    //     cs: constraint system
    //     urs: universal reference string
    //     RETURN: verification status
    pub fn verify(
        &mut self,
        context: &Vec<u8>,
        cs: &ConstraintSystem<E::Fr>,
        k: &Vec<Option<CsVec<E::Fr>>>,
        urs: &URS<E>,
        rng: &mut OsRng,
    ) -> Result<bool, ProofError> {
        // the helper's transcript of the random oracle argument
        let mut argument = Transcript::new(&[]);
        // batch context for the random oracle argument
        argument.append_message(b"bytes", context);

        // query random scalar challenge from verifier
        let u: E::Fr = argument.challenge();

        // add s(u, X) commitment to the context
        argument.commit_point(&self.sux_comm);

        // query random scalar challenge from verifier
        let v: E::Fr = argument.challenge();

        // evaluate s(X, Y) at (u, v)
        let suv: E::Fr;
        match cs.evaluate_s(u, true) {
            None => return Err(ProofError::SuXvEvalComputation),
            Some(evl) => match evl.evaluate(v) {
                None => return Err(ProofError::SuXvEvalComputation),
                Some(evl) => suv = evl,
            },
        }

        // retrieve random oracle values for multipoint evaluation over the vector
        let mut oracles: Vec<(E::Fr, E::Fr, E::Fr, E::Fr)> = Vec::new();
        for (proof, k) in self.batch.iter().zip(k.iter()) {
            oracles.push(proof.prover.oracles(cs, &k))
        }

        // verify individual proofs vectored over EC pairings
        let mut prfsxy: Vec<(E::Fr, E::Fr, Vec<(E::G1Affine, E::Fr, usize)>, E::G1Affine)> =
            Vec::new();
        let mut prfrx1: Vec<(E::Fr, E::Fr, Vec<(E::G1Affine, E::Fr, usize)>, E::G1Affine)> =
            Vec::new();
        let mut prfbatch: Vec<(E::Fr, E::Fr, Vec<(E::G1Affine, E::Fr, usize)>, E::G1Affine)> =
            Vec::new();
        let mut prfsux: Vec<(E::Fr, E::Fr, Vec<(E::G1Affine, E::Fr, usize)>, E::G1Affine)> =
            Vec::new();

        // verify the proof sux_v_prf against the commitment sux_comm and the computed above evaluation s(u, v)
        prfsux.push((
            v,
            E::Fr::one(),
            vec![(self.sux_comm, suv, cs.a.shape().1 + cs.a.shape().0 + 1)],
            self.sux_v_prf,
        ));

        for ((proof, oracle), k) in self.batch.iter().zip(oracles.iter()).zip(k.iter()) {
            match (&proof.helper, proof.txy(Some(cs.evaluate_k(k.clone(), oracle.1)))) {
                (Err(_), _) => return Err(ProofError::ProverVerification),
                (_, Err(err)) => return Err(err),
                (Ok(helper), Ok(txy)) => {
                    prfsux.push((
                        oracle.1,
                        E::Fr::one(),
                        vec![(
                            self.sux_comm,
                            helper.sxy_u_evl,
                            cs.a.shape().1 + cs.a.shape().0 + 1,
                        )],
                        helper.sux_y_prf,
                    ));
                    prfsxy.push((
                        u,
                        E::Fr::one(),
                        vec![(helper.sxy_comm, helper.sxy_u_evl, cs.a.shape().1 * 2 + 1)],
                        helper.sxy_u_prf,
                    ));
                    prfrx1.push((
                        oracle.2,
                        E::Fr::one(),
                        vec![(
                            proof.prover.rx1_comm,
                            proof.prover.rx1_xy_evl,
                            cs.a.shape().1 + 1,
                        )],
                        proof.prover.rx1_xy_prf,
                    ));
                    prfbatch.push((
                        oracle.0,
                        oracle.3,
                        vec![
                            (proof.prover.txy_comm, txy, urs.gnax.len()),
                            (
                                proof.prover.rx1_comm,
                                proof.prover.rx1_x_evl,
                                cs.a.shape().1 + 1,
                            ),
                            (helper.sxy_comm, helper.sxy_x_evl, cs.a.shape().1 * 2 + 1),
                        ],
                        proof.prover.batch_x_prf,
                    ));
                }
            }
            //if self.batch[i].verify(u, self.sux_comm, cs, urs) == false {return Err(ProofError::ProverVerification);} //This would be if verified individually
        }

        // Verify the assembled vector proofs. First, verify the helper's proofs

        // verify the proof sux_y_prf against the commitment sux_comm and the evaluation sxy_u_evl=s(u, y)
        // verify the proof sxy_u_prf against the commitment sxy_comm and the evaluation sxy_u_evl=s(u, y)
        // verify the proof rx1_xy_prf against the commitment rx1_comm and evaluation rx1_xy_evl
        // verify the proof batch_x_prf against the commitments sxy_comm, rx1_comm & txy_comm and evaluations
        // sxy_x_evl, rx1_x_evl and the computed evaluation t(x, y) of the bivariate polynomial t(X, Y)
        // at the point (x, y)
        if urs.verify(&vec![prfsux, prfsxy, prfrx1, prfbatch], rng) == false {
            return Err(ProofError::ProverVerification);
        }

        Ok(true)
    }
}

