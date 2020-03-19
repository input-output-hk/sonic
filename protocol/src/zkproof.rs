/********************************************************************************************

This source file implements zk-proof primitives.

This primitive is the aggregate of types ProverProof and HelperProof. It represents the
complete individual proof that consists of the prover's and the helper's parts

*********************************************************************************************/

pub use super::batch::{BatchProof, HelperProof, ProofError, ProverProof, RandomOracleArgument};
use circuits::constraint_system::ConstraintSystem;
use commitment::urs::URS;
use pairing::{Engine, Field};
use rand::OsRng;
use sprs::CsVec;

pub struct ZkProof<E: Engine> {
    pub prover: ProverProof<E>,
    pub helper: Result<HelperProof<E>, ProofError>,
}

impl<E: Engine> ZkProof<E> {
    // This function verifies the helper's zk-proof
    //     u: random oracle argument value
    //     sux_comm: commitment to s(u, X) polynomial
    //     cs: constraint system
    //     k: optional public params as vector K update
    //     urs: universal reference string
    //     RETURN: verification status
    pub fn verify(
        &mut self,
        u: E::Fr,
        sux_comm: E::G1Affine,
        cs: &ConstraintSystem<E::Fr>,
        k: Option<CsVec<E::Fr>>,
        urs: &URS<E>,
        rng: &mut OsRng,
    ) -> bool {
        // query random oracle values from verifier
        let (x, y, xy, mask) = self.prover.oracles(cs, &k);

        // evaluate k(Y) at y
        match (&self.helper, self.txy(Some(cs.evaluate_k(k, y)))) {
            (Ok(helper), Ok(txy)) => {
                // First, verify the helper's proof

                // verify the proof sux_y_prf against the commitment sux_comm and the evaluation sxy_u_evl=s(u, y)
                if urs.verify(
                    &vec![
                        vec![(
                            y,
                            E::Fr::one(),
                            vec![(
                                sux_comm,
                                helper.sxy_u_evl,
                                cs.a.shape().1 + cs.a.shape().0 + 1,
                            )],
                            helper.sux_y_prf,
                        )],
                        // verify the proof sxy_u_prf against the commitment sxy_comm and the evaluation sxy_u_evl=s(u, y)
                        vec![(
                            u,
                            E::Fr::one(),
                            vec![(helper.sxy_comm, helper.sxy_u_evl, cs.a.shape().1 * 2 + 1)],
                            helper.sxy_u_prf,
                        )],
                        // Second, verify the prover's proof
                        // verify the proof rx1_xy_prf against the commitment rx1_comm and evaluation rx1_xy_evl
                        vec![(
                            xy,
                            E::Fr::one(),
                            vec![(
                                self.prover.rx1_comm,
                                self.prover.rx1_xy_evl,
                                cs.a.shape().1 + 1,
                            )],
                            self.prover.rx1_xy_prf,
                        )],
                        // verify the proof batch_x_prf against the commitments sxy_comm, rx1_comm & txy_comm and evaluations
                        // sxy_x_evl, rx1_x_evl and the computed evaluation t(x, y) of the bivariate polynomial t(X, Y)
                        // at the point (x, y)
                        vec![(
                            x,
                            mask,
                            vec![
                                (self.prover.txy_comm, txy, urs.gnax.len()),
                                (
                                    self.prover.rx1_comm,
                                    self.prover.rx1_x_evl,
                                    cs.a.shape().1 + 1,
                                ),
                                (helper.sxy_comm, helper.sxy_x_evl, cs.a.shape().1 * 2 + 1),
                            ],
                            self.prover.batch_x_prf,
                        )],
                    ],
                    rng,
                ) == false
                {
                    self.helper = Err(ProofError::ProverVerification);
                    return false;
                }
            }
            (_, _) => return false,
        }
        true
    }

    // This function evaluation of t(X, Y) polynomial at (x, y)
    //     ky: k(Y) polynomial eavluation
    //     RETURN: prepared verification context:
    //         x: random oracle value
    //         y: random oracle value
    //         xy: random oracle value product
    //         mask: random oracle masking value
    //         txy: t(X, Y) evaluation at (x, y)
    pub fn txy(&self, ky: Option<E::Fr>) -> Result<E::Fr, ProofError> {
        match &self.helper {
            Err(_) => return Err(ProofError::HelperVerification),
            Ok(helper) => {
                match ky {
                    Some(ky) => {
                        // compute the evaluation of polynomial t(X, Y) at the point (x, y)
                        let mut txy = self.prover.rx1_xy_evl;
                        txy.add_assign(&helper.sxy_x_evl);
                        txy.mul_assign(&self.prover.rx1_x_evl);
                        txy.sub_assign(&ky);
                        Ok(txy)
                    }
                    None => return Err(ProofError::TXyxEvalComputation),
                }
            }
        }
    }
}
