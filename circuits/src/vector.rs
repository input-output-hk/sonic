/***********************************************************************

This source file implements dense representation of sparse vectors.

***********************************************************************/

use pairing::Field;
use sprs::CsVec;
use std::ops::Index;

#[derive(Clone)]
pub struct DenseVector<F> {
    pub value: CsVec<F>,
    zero: F,
}

pub enum Operation {
    Set,
    Add,
    Sub,
}

impl<F> Index<usize> for DenseVector<F>
where
    F: Field,
{
    type Output = F;
    fn index(&self, index: usize) -> &F {
        match self.value.get(index) {
            None => &self.zero,
            Some(x) => x,
        }
    }
}

pub trait SparseVector<F: Field> {
    fn new(len: usize) -> Self;
    fn create(size: usize, index: Vec<usize>, value: Vec<F>) -> Self;
    fn append(&mut self, index: &[usize], value: &[F]);
    fn len(&self) -> usize;
}

impl<F: Field> SparseVector<F> for DenseVector<F> {
    fn new(len: usize) -> Self {
        DenseVector {
            value: CsVec::<F>::empty(len),
            zero: F::zero(),
        }
    }

    fn create(size: usize, index: Vec<usize>, value: Vec<F>) -> Self {
        DenseVector {
            value: CsVec::<F>::new(size, index, value),
            zero: F::zero(),
        }
    }

    fn append(&mut self, index: &[usize], value: &[F]) {
        for (i, v) in index.iter().zip(value) {
            self.value.append(*i, *v);
        }
    }

    fn len(&self) -> usize {
        self.value.dim()
    }
}
