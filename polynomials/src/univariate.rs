/*****************************************************************************************************************

This source file implements the univariate polynomial primitive.

*****************************************************************************************************************/

use pairing::{Field, PrimeField};
use std::iter::FromIterator;
use std::ops::Neg;

#[derive(Clone)]
pub struct Univariate<F: Field> {
    pub neg: Vec<F>,
    pub pos: Vec<F>,
    // TODO: Simplify with more consise definition of Laurent
    // polynomial as a single vector with the integer shift factor
}

impl<F: PrimeField> Univariate<F> {
    // This function evaluates the polynomial at a field element value with Horner's method
    //     elm: field element to evaluate at
    //     RETURN: evaluation field element result
    //     NOTE: Sparse polynomial evaluation can be more efficient with exponentiation
    //           optimized with square-and-add method which is log(N).
    pub fn evaluate(&self, elm: F) -> Option<F> {
        let mut result = F::zero();
        if self.pos.len() > 0 {
            let n = self.pos.len() - 1;
            result = self.pos[n];
            for i in 0..n {
                result.mul_assign(&elm);
                result.add_assign(&self.pos[n - i - 1]);
            }
        }

        if self.neg.len() < 2 {
            return Some(result);
        }
        let n = self.neg.len() - 1;

        match elm.inverse() {
            Some(inv) => {
                let mut neg = self.neg[n];
                for i in 0..n - 1 {
                    neg.mul_assign(&inv);
                    neg.add_assign(&self.neg[n - i - 1]);
                }
                neg.mul_assign(&inv);
                result.add_assign(&neg);
                Some(result)
            }
            None => None,
        }
    }

    // This function multiplies this polynomial by the other
    //    other: the other polynomial
    //    result: result reference
    //    RETURN: multiplication status
    pub fn mul(&self, other: &Self) -> Self {
        // contract the polynomials
        let (self1, sn) = self.contract();
        let (other1, on) = other.contract();
        let n = sn + on;

        let sp = self.pos.len();
        let op = other.pos.len();
        let p = if sp + op == 0 { 0 } else { sp + op - 1 };

        // transform the vectors
        let mut trnsfm1 = Self::dft(self1.pos, Some(n + p), false);
        let trnsfm2 = Self::dft(other1.pos, Some(n + p), false);

        for (trns1, trns2) in trnsfm1.iter_mut().zip(trnsfm2.iter()) {
            trns1.mul_assign(trns2);
        }

        // interpolate the result
        let mut product = Self::dft(trnsfm1, None, true);
        product.resize(n + p, F::zero());
        let result = Self {
            neg: vec![F::zero(); 1],
            pos: product,
        };

        // expand the polynomial
        result.expand(n as isize)
    }

    // This function divides the polynomial difference: (F(x)-F(elm))/(x-elm) in linear time
    // The algorithm adea is borrowed from https://github.com/zknuckles/sonic
    //    elm: base field element
    //    RETURN: resulting polynomial product
    pub fn divide(&self, mut elm: F) -> Option<Self> {
        elm.negate();
        let mut pos = vec![F::zero(); self.pos.len() - 1];
        let mut rcff = F::zero();
        for (x, y) in self.pos.iter().rev().zip(pos.iter_mut().rev()) {
            *y = *x;
            y.sub_assign(&rcff);
            rcff = *y;
            rcff.mul_assign(&elm);
        }

        elm.negate();
        match elm.inverse() {
            Some(inv) => {
                rcff = F::zero();
                let mut neg = vec![F::zero(); self.neg.len()];
                for (x, y) in self.neg.iter().rev().zip(neg.iter_mut().rev()) {
                    *y = *x;
                    y.add_assign(&rcff);
                    y.mul_assign(&inv);
                    rcff = *y;
                    y.negate();
                }
                Some(Self { neg: neg, pos: pos })
            }
            None => None,
        }
    }

    // This function computes Discrete Fourier Transform of the vector
    //    rou: root of unity for the transform
    //    sz: optional evaluation size
    //    RETURN: Fourier Transform of the vector
    pub fn dft(mut vec: Vec<F>, sz: Option<usize>, reverse: bool) -> Vec<F> {
        let n = vec.len();
        // compute the nearest 2^ above and the root of unity for the transform
        let (mut prou, size, log) = Self::rou(if sz.is_none() { n } else { sz.unwrap() });

        // pad the vector to the nearest power of 2 size
        vec.resize(size, F::zero());

        if reverse == true {
            prou = prou.inverse().unwrap();
        }

        // primitive roots of unity have to be such that rou^len=1
        let mut prsou: Vec<F> = vec![F::zero(); log];
        for i in 0..log {
            prou.square();
            prsou[log - i - 1] = prou;
        }

        // divide and conquer recursively to compute the transform's coefficients
        fn dft<F: Field>(input: &Vec<F>, rou: &Vec<F>, log: usize) -> Vec<F> {
            let n = input.len();
            if n == 1 {
                vec![input[0]]
            } else {
                let mut w = F::one();
                // NOTE: this could be optimized without new vector allocation
                // with index calculation [passing on to each recursion step
                let mut input0: Vec<F> = vec![F::zero(); n / 2];
                let mut input1: Vec<F> = vec![F::zero(); n / 2];
                for i in 0..n / 2 {
                    input0[i] = input[i * 2];
                    input1[i] = input[i * 2 + 1];
                }
                let output0 = dft::<F>(&input0, rou, log - 1);
                let output1 = dft::<F>(&input1, rou, log - 1);
                let mut output: Vec<F> = vec![F::zero(); n];
                for i in 0..n / 2 {
                    let mut out = output1[i];
                    out.mul_assign(&w);
                    output[i] = output0[i];
                    output[i].add_assign(&out);
                    output[i + n / 2] = output0[i];
                    output[i + n / 2].sub_assign(&out);
                    w.mul_assign(&rou[log - 1]);
                }
                output
            }
        };
        let mut result = dft::<F>(&vec, &prsou, log);
        if reverse == false {
            return result;
        }

        // for reverse transform, scale the result by the vector size
        let size = F::from_str(&format!("{}", result.len()))
            .unwrap()
            .inverse()
            .unwrap();
        for i in 0..result.len() {
            result[i].mul_assign(&size);
        }
        result
    }

    // This function computes n-th primitive root of unity as the generator of n-muiltiplicative subgroup of rous
    //    len: interpolation size
    //    RETURN: root of unity, size and log for the transform
    pub fn rou(len: usize) -> (F, usize, usize) {
        // compute the nearest 2^ above and the primitive root of unity for the transform
        let mut size = 1;
        let mut log: usize = 0;
        let mut prou = F::root_of_unity();
        while size < len {
            size <<= 1;
            log += 1;
        }
        for _ in log..F::S as usize - 1 {
            prou.square()
        }
        (prou, size, log)
    }

    // This function contracts the given polynomial
    pub fn contract(&self) -> (Self, usize) {
        let mut n = self.neg.len();
        let mut vec = vec![F::zero(); 0];
        if n > 1 {
            vec = Vec::from_iter(self.neg[1..n].iter().cloned());
            vec.reverse();
        } else {
            n = 1
        }
        vec.append(&mut self.pos.clone());
        (
            Self {
                neg: vec![F::zero(); 1],
                pos: vec,
            },
            n - 1,
        )
    }

    // This function expands the given polynomial
    pub fn expand(&self, i: isize) -> Self {
        let (n, p) = (self.neg.len(), self.pos.len());
        let s: usize = if i > 0 { i as usize } else { i.neg() as usize };
        let (mut neg, mut pos): (Vec<F>, Vec<F>);

        if i > 0 {
            neg = Vec::from_iter(self.pos[0..if s > p { p } else { s }].iter().cloned());
            if s > p {
                neg.resize(s, F::zero())
            }
            neg.resize(neg.len() + 1, F::zero());
            neg.reverse();
            neg.append(&mut Vec::from_iter(self.neg[1..n].iter().cloned()));

            if s < p {
                pos = Vec::from_iter(self.pos[s..p].iter().cloned())
            } else {
                pos = vec![F::zero()]
            }
        } else if i < 0 {
            pos = Vec::from_iter(self.neg[1..if s > n { n } else { s }].iter().cloned());
            if s > n - 1 {
                pos.resize(s, F::zero())
            }
            pos.reverse();
            pos.append(&mut Vec::from_iter(self.pos[0..p].iter().cloned()));

            neg = vec![F::zero()];
            if s < n {
                neg.append(&mut Vec::from_iter(self.pos[s + 1..n].iter().cloned()))
            }
        } else {
            neg = self.neg.clone();
            pos = self.pos.clone();
        }
        let result = Self { neg: neg, pos: pos };
        //result.truncate();
        result
    }

    // This function creates a positive polynomial from a vector
    pub fn polynom(vec: Vec<F>) -> Self {
        Self {
            neg: vec![F::zero(); 1],
            pos: vec,
        }
    }

    // This function multiplies this polynomial by a scalar
    //    elm: multiplication scalar
    pub fn mul_assign(&self, elm: F) -> Self {
        let mut ret = self.clone();
        for x in ret.neg.iter_mut() {
            x.mul_assign(&elm);
        }
        for x in ret.pos.iter_mut() {
            x.mul_assign(&elm);
        }
        ret
    }

    // This function adds this polynomial to the other
    //    other: the other polynomial
    //    RETURN: resulting polynomial sum
    pub fn add_alloc(&self, other: &Self) -> Self {
        let n = if self.neg.len() > other.neg.len() {
            self.neg.len()
        } else {
            other.neg.len()
        };
        let p = if self.pos.len() > other.pos.len() {
            self.pos.len()
        } else {
            other.pos.len()
        };
        let zero = F::zero();

        let mut m = Self {
            neg: vec![F::zero(); n],
            pos: vec![F::zero(); p],
        };
        for i in 0..n {
            m.neg[i].add_assign(if i >= self.neg.len() {
                &zero
            } else {
                &self.neg[i]
            });
            m.neg[i].add_assign(if i >= other.neg.len() {
                &zero
            } else {
                &other.neg[i]
            });
        }
        for i in 0..p {
            m.pos[i].add_assign(if i >= self.pos.len() {
                &zero
            } else {
                &self.pos[i]
            });
            m.pos[i].add_assign(if i >= other.pos.len() {
                &zero
            } else {
                &other.pos[i]
            });
        }
        m
    }

    // This function adds this polynomial to the other
    //    other: the other polynomial
    pub fn add_assign(&mut self, other: &Self) {
        if self.pos.len() < other.pos.len() {
            self.pos.resize(other.pos.len(), F::zero());
        }
        if self.neg.len() < other.neg.len() {
            self.neg.resize(other.neg.len(), F::zero());
        }
        for (x, y) in self.pos.iter_mut().zip(other.pos.iter()) {
            x.add_assign(&y);
        }
        for (x, y) in self.neg.iter_mut().zip(other.neg.iter()) {
            x.add_assign(&y);
        }
    }

    // This function subtracts from this polynomial the other
    //    other: the other polynomial
    pub fn sub_assign(&mut self, other: &Self) {
        if self.pos.len() < other.pos.len() {
            self.pos.resize(other.pos.len(), F::zero());
        }
        if self.neg.len() < other.neg.len() {
            self.neg.resize(other.neg.len(), F::zero());
        }
        for (x, y) in self.pos.iter_mut().zip(other.pos.iter()) {
            x.sub_assign(&y);
        }
        for (x, y) in self.neg.iter_mut().zip(other.neg.iter()) {
            x.sub_assign(&y);
        }
    }

    // This function creates a zero instance of a polynomial of given dimensions
    //    n: max degere of negative x
    //    p: max degere of positive x
    pub fn create(n: usize, p: usize) -> Self {
        Self {
            neg: vec![F::zero(); n],
            pos: vec![F::zero(); p],
        }
    }

    // Helper function
    pub fn truncate(&mut self) {
        let mut vec: Vec<F> = self
            .pos
            .clone()
            .into_iter()
            .rev()
            .skip_while(|&x| x.is_zero())
            .collect();
        vec.reverse();
        if vec.len() == 0 {
            vec = vec![F::zero()]
        }
        self.pos = vec;
        vec = self
            .neg
            .clone()
            .into_iter()
            .rev()
            .skip_while(|&x| x.is_zero())
            .collect();
        vec.reverse();
        if vec.len() == 0 {
            vec = vec![F::zero()]
        }
        self.neg = vec;
    }
}
