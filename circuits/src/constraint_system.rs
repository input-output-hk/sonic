/*****************************************************************************************************************

This source file implements Sonic Constraint System primitive.

Sonic constraint system is defined by:
    Labeling of the circuit wires that provide input and carry output values to/from the multiplicative gates of
    the circuit. The labeling is defined as three vectors of wire labels:
        Left input A
        Right input B
        Output C
    Set of linear constraint equations on the set of wire labels with coefficients
        Set of left input coefficient vectors U
        Set of right input coefficient vectors V
        Set of output coefficient vectors W
        Set of scalar values k
Given the above, Sonic constrains the proved statement computation with:
    Multiplicative constraint system of equations
        AxB=C
    Linear constraint system of equations
        A*U+B*V+C*W=k
for any assignment of values to the variables A, B & C of the constrained computation that satisfy the computation
circuit. Here x means Hadamard (component-wise) Vector Multiplication and * means Cartesian Vector Multiplication.
Sonic constraint system is defined as the wire label vectors and sets of linear constraint vectors and scalar values:
    a = […]
    b = […]
    c = […]
    u = [[…], …, […]]
    v = [[…], …, […]]
    w = [[…], …, […]]
    k = […]

*****************************************************************************************************************/
extern crate bincode;

pub use super::gate::CircuitGate;
pub use super::witness::Witness;
use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
use pairing::{Field, PrimeField};
use polynomials::univariate::Univariate;
use sprs::{CsMat, CsVec, CsVecView};
use std::fmt;
use std::io::{self, Read, Write};

#[derive(Clone)]
pub struct ConstraintSystem<F: Field> {
    pub a: CsMat<F>, // left input wire coefficients
    pub b: CsMat<F>, // right input wire coefficients
    pub c: CsMat<F>, // output wire coefficients
    pub k: CsVec<F>, // public parameters
}

impl<F: PrimeField> ConstraintSystem<F> {
    // This function creates CS instance for given depth n
    //     n: depth of the circuit
    pub fn create(n: usize) -> Self {
        Self {
            a: CsMat::<F>::zero((0, n)),
            b: CsMat::<F>::zero((0, n)),
            c: CsMat::<F>::zero((0, n)),
            k: CsVec::<F>::empty(0),
        }
    }

    // this function appends sparse row to the matrix
    pub fn append(&mut self, matrix: char, index: &[usize], value: &[F]) {
        match matrix {
            'a' => {
                let len = self.a.shape().1;
                let f = std::mem::replace(&mut self.a, CsMat::<F>::zero((0, 0)));
                self.a = f.append_outer_csvec(CsVecView::<F>::new_view(len, index, value).unwrap());
            }
            'b' => {
                let len = self.b.shape().1;
                let f = std::mem::replace(&mut self.b, CsMat::<F>::zero((0, 0)));
                self.b = f.append_outer_csvec(CsVecView::<F>::new_view(len, index, value).unwrap());
            }
            'c' => {
                let len = self.c.shape().1;
                let f = std::mem::replace(&mut self.c, CsMat::<F>::zero((0, 0)));
                self.c = f.append_outer_csvec(CsVecView::<F>::new_view(len, index, value).unwrap());
            }
            _ => {}
        }
    }

    pub fn append_to_k(
        &mut self,
        dimension: usize,
        vector_of_indices: &[usize],
        vector_of_values: &[F],
    ) {
        self.k = CsVec::<F>::new(
            self.k.dim() + dimension,
            [self.k.indices(), vector_of_indices].concat(),
            [self.k.data(), vector_of_values].concat(),
        );
    }

    // This function evaluates sparse k polynomial
    pub fn evaluate_k(&self, k: Option<CsVec<F>>, elm: F) -> F {
        let mut rslt = F::zero();
        let kv: CsVec<F> = match k
        {
            Some(kv) => kv,
            None => self.k.clone()
        };

        for x in kv.iter() {
            let mut monom = *x.1;
            monom.mul_assign(&elm.pow(&[(x.0 + self.a.shape().1 + 1) as u64]));
            rslt.add_assign(&monom);
        }
        rslt
    }

    // This function evaluates sparse s polynomial at (x, Y)
    // TODO: benchmark the evaluation performance for large circuits with the two different implementations below
    pub fn evaluate_sxy(&self, x: F, y: F) -> Option<F> {
        match (x.inverse(), y.inverse()) {
            (Some(xi), Some(yi)) => {
                let shape = self.a.shape();

                // precompute powers of parameters and inverses
                let mut yp = vec![F::zero(); shape.0];
                yp[0] = y.pow([(shape.1 + 1) as u64]);
                for i in 1..shape.0 {
                    yp[i] = yp[i - 1];
                    yp[i].mul_assign(&y);
                }
                let mut xp = vec![F::zero(); shape.0 + shape.1];
                xp[0] = x;
                for i in 1..shape.0 + shape.1 {
                    xp[i] = xp[i - 1];
                    xp[i].mul_assign(&x);
                }
                let mut xpi = vec![F::zero(); shape.1];
                xpi[0] = xi;
                for i in 1..shape.1 {
                    xpi[i] = xpi[i - 1];
                    xpi[i].mul_assign(&xi);
                }

                let mut rslt = F::zero();

                for entry in self.a.iter() {
                    let mut monom = *entry.0;
                    monom.mul_assign(&xpi[(entry.1).1]);
                    monom.mul_assign(&yp[(entry.1).0]);
                    rslt.add_assign(&monom);
                }
                for entry in self.b.iter() {
                    let mut monom = *entry.0;
                    monom.mul_assign(&xp[(entry.1).1]);
                    monom.mul_assign(&yp[(entry.1).0]);
                    rslt.add_assign(&monom);
                }
                for entry in self.c.iter() {
                    let mut monom = *entry.0;
                    monom.mul_assign(&xp[(entry.1).1 + shape.0]);
                    monom.mul_assign(&yp[(entry.1).0]);
                    rslt.add_assign(&monom);
                }
                let mut xy = x;
                xy.mul_assign(&y);
                let mut xyi = x;
                xyi.mul_assign(&yi);

                let mut xpy = x.pow([(shape.1) as u64]);
                let mut xny = xpy;
                for _ in 0..shape.1 {
                    xpy.mul_assign(&xy);
                    rslt.sub_assign(&xpy);
                    xny.mul_assign(&xyi);
                    rslt.sub_assign(&xny);
                }

                return Some(rslt);
            }
            (_, _) => return None,
        }
    }

    /*
    pub fn evaluate_sxy(&self, x: F, y: F) -> Option<F> {
        match (x.inverse(), y.inverse()) {
            (Some(xi), Some(yi)) => {
                let mut rslt = F::zero();
                let shape = self.a.shape();

                for entry in self.a.iter() {
                    let xp = xi.pow([((entry.1).1 + 1) as u64]);
                    let yp = y.pow([((entry.1).0 + shape.1 + 1) as u64]);
                    let mut monom = *entry.0;
                    monom.mul_assign(&xp);
                    monom.mul_assign(&yp);
                    rslt.add_assign(&monom);
                }
                for entry in self.b.iter() {
                    let xp = x.pow([((entry.1).1 + 1) as u64]);
                    let yp = y.pow([((entry.1).0 + shape.1 + 1) as u64]);
                    let mut monom = *entry.0;
                    monom.mul_assign(&xp);
                    monom.mul_assign(&yp);
                    rslt.add_assign(&monom);
                }
                for entry in self.c.iter() {
                    let xp = x.pow([((entry.1).1 + shape.0 + 1) as u64]);
                    let yp = y.pow([((entry.1).0 + shape.1 + 1) as u64]);
                    let mut monom = *entry.0;
                    monom.mul_assign(&xp);
                    monom.mul_assign(&yp);
                    rslt.add_assign(&monom);
                }
                let mut xy = x;
                xy.mul_assign(&y);
                let mut xyi = x;
                xyi.mul_assign(&yi);

                let mut xpy = x.pow([(shape.1) as u64]);
                let mut xny = xpy;
                for _ in 0..shape.1 {
                    xpy.mul_assign(&xy);
                    rslt.sub_assign(&xpy);
                    xny.mul_assign(&xyi);
                    rslt.sub_assign(&xny);
                }

                return Some(rslt);
            }
            (_, _) => return None,
        }
    }
    */

    // This function evaluates sparse s polynomial against one variable value
    pub fn evaluate_s(&self, elm: F, var: bool) -> Option<Univariate<F>> {
        match elm.inverse() {
            None => return None,
            Some(inv) => {
                let shape = self.a.shape();
                if var == false {
                    let mut rslt = Univariate::<F>::create(shape.1 + 1, 2 * shape.1 + 1);

                    let mut y = F::one();
                    let mut yp = vec![F::zero(); shape.0 + shape.1];
                    for x in yp.iter_mut() {
                        y.mul_assign(&elm);
                        *x = y
                    }

                    y = F::one();
                    let mut yn = vec![F::zero(); shape.1];
                    for x in yn.iter_mut() {
                        y.mul_assign(&inv);
                        *x = y
                    }

                    for entry in self.a.iter() {
                        let mut monom = *entry.0;
                        monom.mul_assign(&yp[(entry.1).0 + shape.1]);
                        rslt.neg[(entry.1).1 + 1].add_assign(&monom);
                    }
                    for entry in self.b.iter() {
                        let mut monom = *entry.0;
                        monom.mul_assign(&yp[(entry.1).0 + shape.1]);
                        rslt.pos[(entry.1).1 + 1].add_assign(&monom);
                    }
                    for entry in self.c.iter() {
                        let mut monom = *entry.0;
                        monom.mul_assign(&yp[(entry.1).0 + shape.1]);
                        rslt.pos[(entry.1).1 + shape.1 + 1].add_assign(&monom);
                    }
                    for i in 0..shape.1 {
                        rslt.pos[i + shape.1 + 1].sub_assign(&yp[i]);
                        rslt.pos[i + shape.1 + 1].sub_assign(&yn[i]);
                    }
                    return Some(rslt);
                } else {
                    let mut rslt = Univariate::<F>::create(shape.1 + 1, shape.0 + shape.1 + 1);

                    let mut x = F::one();
                    let mut xp = vec![F::zero(); 2 * shape.1];
                    for y in xp.iter_mut() {
                        x.mul_assign(&elm);
                        *y = x
                    }

                    x = F::one();
                    let mut xn = vec![F::zero(); shape.1];
                    for y in xn.iter_mut() {
                        x.mul_assign(&inv);
                        *y = x
                    }

                    for entry in self.a.iter() {
                        let mut monom = *entry.0;
                        monom.mul_assign(&xn[(entry.1).1]);
                        rslt.pos[(entry.1).0 + shape.1 + 1].add_assign(&monom);
                    }
                    for entry in self.b.iter() {
                        let mut monom = *entry.0;
                        monom.mul_assign(&xp[(entry.1).1]);
                        rslt.pos[(entry.1).0 + shape.1 + 1].add_assign(&monom);
                    }
                    for entry in self.c.iter() {
                        let mut monom = *entry.0;
                        monom.mul_assign(&xp[shape.1 + (entry.1).1]);
                        rslt.pos[(entry.1).0 + shape.1 + 1].add_assign(&monom);
                    }
                    for i in 0..shape.1 {
                        rslt.pos[i + 1].sub_assign(&xp[i + shape.1]);
                        rslt.neg[i + 1].sub_assign(&xp[i + shape.1]);
                    }
                    return Some(rslt);
                }
            }
        }
    }

    // This function verifies the consistency of the wire assignements (witness) against the constraints
    //     witness: wire assignement witness
    //     k: optional public params as vector K update
    //     RFTURN: verification status
    pub fn verify(&self, k: Option<CsVec<F>>, witness: &Witness<F>) -> bool {
        let kv: CsVec<F> = match k
        {
            Some(kv) => kv,
            None => self.k.clone()
        };

        // verify the witness against the multiplicative constraints
        for wt in witness.gates.iter() {
            let mut ab = wt.a;
            ab.mul_assign(&wt.b);
            if ab != wt.c {
                return false;
            }
        }

        if self.a.shape().1 != witness.gates.len()
            || self.b.shape().1 != witness.gates.len()
            || self.c.shape().1 != witness.gates.len()
            || self.a.shape().0 != self.b.shape().0
            || self.b.shape().0 != self.c.shape().0
        {
            return false;
        }

        // verify the witness against the linear constraints
        for ((row, a), (b, c)) in self
            .a
            .outer_iterator()
            .enumerate()
            .zip(self.b.outer_iterator().zip(self.c.outer_iterator()))
        {
            let mut acc = F::zero();
            for (col, constraint) in a.iter() {
                let mut vc = witness.gates[col].a;
                if !vc.is_zero() {
                    vc.mul_assign(&constraint);
                    acc.add_assign(&vc)
                }
            }
            for (col, constraint) in b.iter() {
                let mut vc = witness.gates[col].b;
                if !vc.is_zero() {
                    vc.mul_assign(&constraint);
                    acc.add_assign(&vc)
                }
            }
            for (col, constraint) in c.iter() {
                let mut vc = witness.gates[col].c;
                if !vc.is_zero() {
                    vc.mul_assign(&constraint);
                    acc.add_assign(&vc)
                }
            }
            if acc != match kv.get(row) {
                    None => F::zero(),
                    Some(x) => *x,
                }
            {
                return false;
            }
        }
        true
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        // write a
        writer.write_u32::<BigEndian>(self.a.rows() as u32)?;
        writer.write_u32::<BigEndian>(self.a.cols() as u32)?;

        writer.write_u32::<BigEndian>(self.a.indptr().len() as u32)?;
        for index in self.a.indptr().iter().cloned() {
            writer.write_u32::<BigEndian>(index as u32)?;
        }

        writer.write_u32::<BigEndian>(self.a.indices().len() as u32)?;
        for index in self.a.indices().iter().cloned() {
            writer.write_u32::<BigEndian>(index as u32)?;
        }

        writer.write_u32::<BigEndian>(self.a.data().len() as u32)?;
        for item in &self.a.data()[..] {
            for digit in item.into_repr().as_ref().iter().rev() {
                writer.write_u64::<BigEndian>(*digit)?;
            }
        }

        // write b
        writer.write_u32::<BigEndian>(self.b.rows() as u32)?;
        writer.write_u32::<BigEndian>(self.b.cols() as u32)?;

        writer.write_u32::<BigEndian>(self.b.indptr().len() as u32)?;
        for index in self.b.indptr().iter().cloned() {
            writer.write_u32::<BigEndian>(index as u32)?;
        }

        writer.write_u32::<BigEndian>(self.b.indices().len() as u32)?;
        for index in self.b.indices().iter().cloned() {
            writer.write_u32::<BigEndian>(index as u32)?;
        }

        writer.write_u32::<BigEndian>(self.b.data().len() as u32)?;
        for item in &self.b.data()[..] {
            for digit in item.into_repr().as_ref().iter().rev() {
                writer.write_u64::<BigEndian>(*digit)?;
            }
        }

        // write c
        writer.write_u32::<BigEndian>(self.c.rows() as u32)?;
        writer.write_u32::<BigEndian>(self.c.cols() as u32)?;

        writer.write_u32::<BigEndian>(self.c.indptr().len() as u32)?;
        for index in self.c.indptr().iter().cloned() {
            writer.write_u32::<BigEndian>(index as u32)?;
        }

        writer.write_u32::<BigEndian>(self.c.indices().len() as u32)?;
        for index in self.c.indices().iter().cloned() {
            writer.write_u32::<BigEndian>(index as u32)?;
        }

        writer.write_u32::<BigEndian>(self.c.data().len() as u32)?;
        for item in &self.c.data()[..] {
            for digit in item.into_repr().as_ref().iter().rev() {
                writer.write_u64::<BigEndian>(*digit)?;
            }
        }

        // write k
        writer.write_u32::<BigEndian>(self.k.dim() as u32)?;

        writer.write_u32::<BigEndian>(self.k.indices().len() as u32)?;
        for index in self.k.indices().iter().cloned() {
            writer.write_u32::<BigEndian>(index as u32)?;
        }

        writer.write_u32::<BigEndian>(self.k.data().len() as u32)?;
        for item in &self.k.data()[..] {
            for digit in item.into_repr().as_ref().iter().rev() {
                writer.write_u64::<BigEndian>(*digit)?;
            }
        }

        Ok(())
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let read_field_element = |reader: &mut R| -> io::Result<F> {
            let mut repr = <F as PrimeField>::Repr::default();
            for digit in repr.as_mut().iter_mut().rev() {
                *digit = reader.read_u64::<BigEndian>()?;
            }
            repr.as_mut()[3] &= 0x7fffffffffffffff;

            Ok(F::from_repr(repr).unwrap())
        };

        let a: CsMat<F>;
        let b: CsMat<F>;
        let c: CsMat<F>;
        let k: CsVec<F>;

        // read a
        {
            let rows = reader.read_u32::<BigEndian>()? as usize;
            let cols = reader.read_u32::<BigEndian>()? as usize;

            let mut indptr = vec![];
            let mut indices = vec![];
            let mut data = vec![];

            let indptr_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..indptr_len {
                indptr.push(reader.read_u32::<BigEndian>()? as usize)
            }

            let indices_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..indices_len {
                indices.push(reader.read_u32::<BigEndian>()? as usize)
            }

            let data_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..data_len {
                data.push(read_field_element(&mut reader)?)
            }
            a = CsMat::new((rows, cols), indptr, indices, data)
        }

        // read b
        {
            let rows = reader.read_u32::<BigEndian>()? as usize;
            let cols = reader.read_u32::<BigEndian>()? as usize;

            let mut indptr = vec![];
            let mut indices = vec![];
            let mut data = vec![];

            let indptr_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..indptr_len {
                indptr.push(reader.read_u32::<BigEndian>()? as usize)
            }

            let indices_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..indices_len {
                indices.push(reader.read_u32::<BigEndian>()? as usize)
            }

            let data_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..data_len {
                data.push(read_field_element(&mut reader)?)
            }
            b = CsMat::new((rows, cols), indptr, indices, data)
        }

        // read c
        {
            let rows = reader.read_u32::<BigEndian>()? as usize;
            let cols = reader.read_u32::<BigEndian>()? as usize;

            let mut indptr = vec![];
            let mut indices = vec![];
            let mut data = vec![];

            let indptr_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..indptr_len {
                indptr.push(reader.read_u32::<BigEndian>()? as usize)
            }

            let indices_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..indices_len {
                indices.push(reader.read_u32::<BigEndian>()? as usize)
            }

            let data_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..data_len {
                data.push(read_field_element(&mut reader)?)
            }
            c = CsMat::new((rows, cols), indptr, indices, data)
        }

        // read k
        {
            let dim = reader.read_u32::<BigEndian>()? as usize;

            let mut indices = vec![];
            let mut data = vec![];

            let indices_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..indices_len {
                indices.push(reader.read_u32::<BigEndian>()? as usize)
            }

            let data_len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..data_len {
                data.push(read_field_element(&mut reader)?)
            }
            k = CsVec::<F>::new(dim, indices, data);
        }

        Ok(ConstraintSystem::<F> { a, b, c, k })
    }
}

impl<F: Field> PartialEq for ConstraintSystem<F> {
    fn eq(&self, other: &Self) -> bool {
        if self.a != other.a || self.b != other.b || self.c != other.c || self.k != other.k {
            return false;
        }
        return true;
    }
}

impl<F: Field> fmt::Debug for ConstraintSystem<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Constraint system: {:?}, {:?}, {:?}, {:?}",
            self.a, self.b, self.c, self.k
        )
    }
}
