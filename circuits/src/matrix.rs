/***********************************************************************

This source file implements dense representation of sparse matrix.

***********************************************************************/

pub use super::vector::{DenseVector, SparseVector};
use pairing::Field;
use sprs::{CsMat, CsVecView};
use std::ops::Index;

#[derive(Clone)]
pub struct DenseMatrix<F> {
    pub value: CsMat<F>,
    zero: F,
}

impl<F> Index<(usize, usize)> for DenseMatrix<F>
where
    F: Field,
{
    type Output = F;
    fn index(&self, index: (usize, usize)) -> &F {
        match self.value.get(index.0, index.1) {
            None => &self.zero,
            Some(x) => x,
        }
    }
}

pub trait SparseMatrix<F: Field> {
    fn new(depth: usize, width: usize) -> Self;
    fn shape(&self) -> (usize, usize);
    fn append(&mut self, index: &[usize], value: &[F]);
    fn insert(&mut self, row: usize, col: usize, value: F);
}

impl<F: Field> SparseMatrix<F> for DenseMatrix<F> {
    fn new(depth: usize, width: usize) -> Self {
        Self {
            value: CsMat::<F>::zero((depth, width)),
            zero: F::zero(),
        }
    }

    fn shape(&self) -> (usize, usize) {
        (self.value.rows(), self.value.cols())
    }

    fn append(&mut self, index: &[usize], value: &[F]) {
        let len = self.value.shape().1;
        let f = std::mem::replace(&mut self.value, CsMat::<F>::zero((0, 0)));
        self.value = f.append_outer_csvec(CsVecView::<F>::new_view(len, index, value).unwrap());
    }

    fn insert(&mut self, row: usize, col: usize, value: F) {
        self.value.insert(row, col, value);
    }
}
