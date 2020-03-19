/*****************************************************************************************************************

This source file implements the random oracle argument API for Sonic. The idea and the implementation of the use
of Merlin create for Fiat-Shamir heuristic is borrowed from https://github.com/zknuckles/sonic

*****************************************************************************************************************/

use merlin::Transcript;
use pairing::{CurveAffine, PrimeField, PrimeFieldRepr};
use std::fmt;
use std::io;

#[derive(Debug)]
pub enum ProofError {
    RX1Computation,
    TXyComputation,
    TXyxEvalComputation,
    TXyxPrfComputation,
    RX1xEvalComputation,
    RX1xPrfComputation,
    RX1xyEvalComputation,
    RX1xyPrfComputation,
    SXyComputation,
    SXyxEvalComputation,
    SXyxPrfComputation,
    SXyuEvalComputation,
    SXyuPrfComputation,
    SuXComputation,
    SuXyPrfComputation,
    SuXvEvalComputation,
    SuXvPrfComputation,
    ProverVerification,
    HelperVerification,
    BatchVerification,
    KyEvalComputation,
}

// Implement `Display` for ProofError
impl fmt::Display for ProofError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({})", self)
    }
}

pub trait RandomOracleArgument {
    fn commit_point<G: CurveAffine>(&mut self, point: &G);
    fn commit_scalar<F: PrimeField>(&mut self, scalar: &F);
    fn challenge<F: PrimeField>(&mut self) -> F;
}

impl RandomOracleArgument for Transcript {
    fn commit_point<G: CurveAffine>(&mut self, point: &G) {
        self.append_message(b"point", point.into_compressed().as_ref());
    }

    fn commit_scalar<F: PrimeField>(&mut self, scalar: &F) {
        let mut v = vec![];
        scalar.into_repr().write_le(&mut v).unwrap();
        self.append_message(b"scalar", &v);
    }

    fn challenge<F: PrimeField>(&mut self) -> F {
        loop {
            let mut repr: F::Repr = Default::default();
            repr.read_be(TranscriptReader(self)).unwrap();
            if let Ok(result) = F::from_repr(repr) {
                if let Some(_) = result.inverse() {
                    return result;
                }
                self.commit_scalar(&result);
            }
        }
    }
}

struct TranscriptReader<'a>(&'a mut Transcript);

impl<'a> io::Read for TranscriptReader<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.challenge_bytes(b"read", buf);

        Ok(buf.len())
    }
}
