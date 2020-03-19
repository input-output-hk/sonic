/*****************************************************************************************************************

This source file implements the Sonic universal reference string primitive

Sonic universal SRS={{g^(x^i)}, {g^(αx^i)}\g^α, {h^(β^i)}, {h^(αx^i)}} updateability enables user updating URS
in such a way that, once the user discards his update trapdoor secrets, no other party is in possession of the
updated trapdoor secrets. This is possible due to the facts that, unlike other SNARKs protocols utilizing
polynomial evaluations in exponents of URS, Sonic only uses evaluations of monomials in its universal URS which
has size linear in the size of the circuit.

In Midnight setting, the use case of this functionality would have to have a special
“configuration” transaction type implemented that would allow a user to generate an update to the trusted setup
in such a way that, from the point on as the transaction gets committed to the ledger, the user can be confident
that no other party possesses the knowledge of the trapdoors of the public setup to generate the false proofs.
With this system, the adversarial attack can only exploit the case when all of the updaters of the public setup
collude collectively and with the original setup generation. As soon as one non-colluding user updates the setup,
the setup becomes secure from the viewpoint of this type of attack. This special transaction contains, together
with the computed setup update, a NIZK proof of the correctness of the update. This proof is verified by all the
peer nodes upon the transaction/block commitment and by miners upon block generation. Once the transaction gets
committed to the ledger, all the subsequent private transactions with zk-SNARKs proofs are computed and verified
against the updated public setup.

*****************************************************************************************************************/

use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
use circuits::constraint_system::ConstraintSystem;
use pairing::EncodedPoint;
use pairing::{CurveAffine, CurveProjective, Engine, Field, PrimeField, PrimeFieldRepr};
use polynomials::univariate::Univariate;
use std::collections::HashMap;
use std::fmt;
use std::io::{self, Read, Write};
use rand::OsRng;
use rayon::prelude::*;

// check pairing of a&b vs pairing of c&d
macro_rules! pairing_check1 {
    ($a:expr, $b:expr, $c:expr, $d:expr) => {
        if <E>::pairing($a, $b) != <E>::pairing($c, $d) {
            return false;
        }
    };
}

// check pairing of a&b vs c
macro_rules! pairing_check2 {
    ($a:expr, $b:expr, $c:expr) => {
        if <E>::pairing($a, $b) != $c {
            return false;
        }
    };
}

// URS update proof
pub struct UpdateProof<E: Engine> {
    pub gx: E::G1Affine,
    pub ga: E::G1Affine,
}

pub struct URS<E: Engine> {
    pub gp1x: Vec<E::G1Affine>,            // g^(x^i) for 0 <= i < d
    pub gn1x: Vec<E::G1Affine>,            // g^(x^i) for -d < i <= 0
    pub gpax: Vec<E::G1Affine>,            // g^(αx^i) for 0 <= i < d, gpax[0]=E::G1::one()
    pub gnax: Vec<E::G1Affine>,            // g^(αx^i) for -d < i <= 0, gnax[0]=E::G1::one()
    pub hn1x: HashMap<usize, E::G2Affine>, // h^(x^i) for -d < i <= 0
    pub hp1x1: E::G2Affine,                // h^(x)
    pub hpax0: E::G2Affine,                // h^(α)
    pub hpax1: E::G2Affine,                // h^(αx)

    // TODO: have to do the complete proof chain
    pub prf: UpdateProof<E>,
}

impl<E: Engine> URS<E> {
    // empty default calback, use as <obj::URS<E>>::callback
    pub fn callback(_i: usize) {}

    // This function creates URS instance for circuits up to depth d
    //     depth: maximal depth of the circuits
    //     xp: trapdoor secret
    //     a: trapdoor secret
    pub fn create(depth: usize, degrees: Vec<usize>, xp: E::Fr, a: E::Fr) -> Self {
        let window_size = if depth < 32 {3} else {(2.0 / 3.0 * (f64::from(depth as u32)).log2() + 2.0).ceil() as usize};
        let g = Self::get_window_table
        (
            E::Fr::NUM_BITS as usize,
            window_size,
            E::G1::one()
        );

        fn table<E: Engine>
        (
            scalar: &Vec<E::Fr>,
            table: &mut Vec<Vec<E::G1>>,
            size: usize
        ) -> Vec<E::G1Affine>
        {
            let mut elm = URS::<E>::multi_scalar_mul
            (
                E::Fr::NUM_BITS as usize,
                size,
                table,
                scalar,
            );
            E::G1::batch_normalization(&mut elm);
            elm.into_iter().map(|e| e.into_affine()).collect()
        }

        let xn = xp.inverse().unwrap();
        let mut gx = E::G1::one();
        gx.mul_assign(xp);

        let mut hp1x1 = E::G2::one();
        hp1x1.mul_assign(xp);
        let mut hpax0 = E::G2::one();
        hpax0.mul_assign(a);
        let mut hpax1 = hpax0;
        hpax1.mul_assign(xp);

        let mut hn1x: HashMap<usize, E::G2Affine> = HashMap::new();
        for degree in degrees.iter() {
            hn1x.insert(depth - *degree, {
                let mut x = E::G2::one();
                x.mul_assign(xn.pow([(depth - *degree) as u64]));
                x.into_affine()
            });
        }

        let mut x =
        [
            (E::Fr::one(), xn),
            (E::Fr::one(), xp),
            (a, xn),
            (a, xp)
        ];

        let powers = x.par_iter_mut().map
        (
            |(s, y)| (0..depth).map(|_| {let ret = *s; s.mul_assign(&y); ret}).collect::<Vec<_>>()

        ).collect::<Vec<_>>();

        let mut urs = URS {
            gn1x: table::<E>(&powers[0], &mut g.clone(), window_size),
            gp1x: table::<E>(&powers[1], &mut g.clone(), window_size),
            gnax: table::<E>(&powers[2], &mut g.clone(), window_size),
            gpax: table::<E>(&powers[3], &mut g.clone(), window_size),

            hn1x,
            hp1x1: hp1x1.into_affine(),
            hpax0: hpax0.into_affine(),
            hpax1: hpax1.into_affine(),

            prf: UpdateProof {
                gx: E::G1Affine::from(gx),
                ga: E::G1Affine::one(), // intentionally erasing this according to the spec
            },
        };

        // Erase the first element from gnax & gpax according to spec
        urs.gnax[0] = E::G1Affine::one();
        urs.gpax[0] = E::G1Affine::one();
        urs
    }

    pub fn create_cs_based(cs: &ConstraintSystem<E::Fr>, xp: E::Fr, a: E::Fr) -> Self
    {
        Self::create
        (
            cs.k.dim() + 4 * cs.a.shape().1 + 8, 
            vec!
            [
                cs.k.dim() + 4 * cs.a.shape().1 + 8,
                cs.a.shape().1 + 1,
                cs.a.shape().1 * 2 + 1,
                cs.a.shape().1 + cs.a.shape().0 + 1,
            ], 
            xp, 
            a
        )
    }

    // This function updates URS instance and computes the update proof
    //     xp: trapdoor secret
    //     a: trapdoor secret
    //     RETURN: computed zk-proof
    pub fn update(&mut self, xp: E::Fr, a: E::Fr) {
        fn exponentiate<C: CurveAffine>(scalar: &Vec<C::Scalar>, urs: &mut Vec<C>)
        {
            urs.par_iter_mut().zip(scalar).for_each
            (
                |(p, s)| {*p = p.mul(s.into_repr()).into_affine()}
            )
        }

        let xn = xp.inverse().unwrap();
        // Compute the URS update

        let mut x =
        [
            (E::Fr::one(), self.gn1x.len(), xn),
            (E::Fr::one(), self.gp1x.len(), xp),
            (a, self.gnax.len(), xn),
            (a, self.gpax.len(), xp)
        ];

        let powers = x.par_iter_mut().map
        (
            |(s, size, y)| (0..*size).map(|_| {let ret = *s; s.mul_assign(&y); ret}).collect::<Vec<_>>()

        ).collect::<Vec<_>>();

        exponentiate(&powers[0], &mut self.gn1x);
        exponentiate(&powers[1], &mut self.gp1x);
        exponentiate(&powers[2], &mut self.gnax);
        exponentiate(&powers[3], &mut self.gpax);

        let mut hp1x1 = self.hp1x1.into_projective();
        hp1x1.mul_assign(xp);
        self.hp1x1 = hp1x1.into_affine();
        let mut hpax0 = self.hpax0.into_projective();
        hpax0.mul_assign(a);
        self.hpax0 = hpax0.into_affine();
        let mut hpax1 = self.hpax1.into_projective();
        hpax1.mul_assign(a);
        hpax1.mul_assign(xp);
        self.hpax1 = hpax1.into_affine();

        for x in self.hn1x.iter_mut() {
            let mut y = x.1.into_projective();
            y.mul_assign(xn.pow([*x.0 as u64]));
            *x.1 = y.into_affine();
        }

        // Erase the first element from gnax & gpax according to spec
        self.gnax[0] = E::G1Affine::one();
        self.gpax[0] = E::G1Affine::one();

        let mut gx = E::G1::one();
        gx.mul_assign(xp);
        let mut ga = E::G1::one();
        ga.mul_assign(a);

        self.prf = UpdateProof {
            gx: E::G1Affine::from(gx),
            ga: E::G1Affine::from(ga),
        }
    }

    // This function verifies the updated URS against the zk-proof and the previous URS instance
    //     exp2[0]: previous URS hp1x[1]
    //     exp2[5]: previous URS hpax[0]
    //     RETURN: zk-proof verification status
    pub fn check<F>(&mut self, hp1x1: E::G2Affine, hpax0: E::G2Affine, callback: F, rng: &mut OsRng) -> bool
    where
        F: Fn(usize),
    {
        // TODO: have to do the complete zk-proof chain verification, not just URS

        let xy = <E>::pairing(E::G1::from(self.prf.gx), E::G2::from(hp1x1));
        let ab = <E>::pairing(<E>::G1::one(), E::G2::from(self.hpax0));

        // verify gp1x[1] consistency with zk-proof
        pairing_check2!(E::G1::from(self.gp1x[1]), E::G2::one(), xy);
        // verify hp1x[1] consistency with zk-proof
        pairing_check2!(E::G1::one(), E::G2::from(self.hp1x1), xy);
        // verify gpax[1] consistency against hpax[1] which is verified inductively from hpax[0]
        pairing_check1!(
            E::G1::from(self.gpax[1]),
            E::G2::one(),
            E::G1::one(),
            E::G2::from(self.hpax1)
        );
        // verify hpax[0] consistency with zk-proof
        pairing_check2!(E::G1::from(self.prf.ga), E::G2::from(hpax0), ab);

        let fk = <E>::pairing(E::G1Affine::one(), E::G2Affine::one());
        for x in self.hn1x.iter() {
            if <E>::pairing(self.gp1x[*x.0], *x.1) != fk {
                return false;
            }
        }

        let mut g0: Vec<(E::G1Affine, E::Fr)> = vec![];
        let mut g1: Vec<(E::G1Affine, E::Fr)> = vec![];

        for i in 1..self.gp1x.len() {
            let randomiser: Vec<E::Fr> = (0..4).map(|_| Univariate::<E::Fr>::rand(rng)).collect();

            // inductively verify gp1x & gn1x from gp1x[1]
            g0.push((self.gp1x[i], randomiser[0]));
            g0.push((self.gn1x[i - 1], randomiser[1]));
            g1.push((self.gp1x[i - 1], randomiser[0]));
            g1.push((self.gn1x[i], randomiser[1]));

            if i != 1
            // this is accounting for the "hole" in the URS
            {
                // inductively verify gpax & gnax from gpax[1]
                g0.push((self.gpax[i], randomiser[2]));
                g0.push((self.gnax[i - 1], randomiser[3]));
                g1.push((self.gpax[i - 1], randomiser[2]));
                g1.push((self.gnax[i], randomiser[3]));
            }
            callback(i);
        }

        let mut table = vec![];
        table.push((Self::multiexp(&g0).prepare(), E::G2Affine::one().prepare()));
        table.push((
            Self::multiexp(&g1).prepare(),
            ({
                let mut neg = self.hp1x1;
                neg.negate();
                neg
            })
            .prepare(),
        ));
        let x: Vec<(
            &<E::G1Affine as CurveAffine>::Prepared,
            &<E::G2Affine as CurveAffine>::Prepared,
        )> = table.iter().map(|x| (&x.0, &x.1)).collect();
        E::final_exponentiation(&E::miller_loop(&x)).unwrap() == E::Fqk::one()
    }

    pub fn get_window_table<T: CurveProjective>(
        scalar_size: usize,
        window: usize,
        g: T,
    ) -> Vec<Vec<T>> {
        let in_window = 1 << window;
        let outerc = (scalar_size + window - 1) / window;
        let last_in_window = 1 << (scalar_size - (outerc - 1) * window);

        let mut multiples_of_g = vec![vec![T::zero(); in_window]; outerc];

        let mut g_outer = g;
        for outer in 0..outerc {
            let mut g_inner = T::zero();
            let cur_in_window = if outer == outerc - 1 {
                last_in_window
            } else {
                in_window
            };
            for inner in 0..cur_in_window {
                multiples_of_g[outer][inner] = g_inner;
                g_inner.add_assign(&g_outer);
            }
            for _ in 0..window {
                g_outer.double();
            }
        }
        multiples_of_g
    }

    pub fn windowed_mul<T: CurveProjective>(
        outerc: usize,
        window: usize,
        multiples_of_g: &[Vec<T>],
        scalar: &T::Scalar,
    ) -> T {
        let mut scalar_repr = scalar.into_repr();
        let scalar_val = (0..<T::Scalar as PrimeField>::NUM_BITS as usize).map
        (
            |_|
            {
                let x = if scalar_repr.as_ref()[0] & 1u64 == 1 {true} else {false};
                scalar_repr.div2();
                x
            }
        ).collect::<Vec<_>>();
        //scalar_val.reverse();

        let mut res = multiples_of_g[0][0];
        for outer in 0..outerc {
            let mut inner = 0usize;
            for i in 0..window {
                if outer * window + i < (<T::Scalar as PrimeField>::NUM_BITS as usize)
                    && scalar_val[outer * window + i]
                {
                    inner |= 1 << i;
                }
            }
            res.add_assign(&multiples_of_g[outer][inner]);
        }
        res
    }

    pub fn multi_scalar_mul<T: CurveProjective>(
        scalar_size: usize,
        window: usize,
        table: &[Vec<T>],
        v: &[T::Scalar],
    ) -> Vec<T> {
        let outerc = (scalar_size + window - 1) / window;
        assert!(outerc <= table.len());

        v.par_iter().map(|e| Self::windowed_mul::<T>(outerc, window, table, e)).collect::<Vec<_>>()
    }

    pub fn write_uncompressed<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_u32::<BigEndian>(self.gp1x.len() as u32)?;
        for g in &self.gp1x[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.gn1x.len() as u32)?;
        for g in &self.gn1x[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.gpax.len() as u32)?;
        for g in &self.gpax[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.gnax.len() as u32)?;
        for g in &self.gnax[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.hn1x.len() as u32)?;
        for (key, val) in self.hn1x.iter() {
            writer.write_u32::<BigEndian>(*key as u32)?;
            writer.write_all((*val).into_uncompressed().as_ref())?;
        }

        writer.write_all(self.hp1x1.into_uncompressed().as_ref())?;
        writer.write_all(self.hpax0.into_uncompressed().as_ref())?;
        writer.write_all(self.hpax1.into_uncompressed().as_ref())?;

        writer.write_all(&self.prf.ga.into_uncompressed().as_ref())?;
        writer.write_all(&self.prf.gx.into_uncompressed().as_ref())?;

        Ok(())
    }

    pub fn read_uncompressed<R: Read>(mut reader: R, checked: bool) -> io::Result<Self> {
        let read_g1_uncompressed = |reader: &mut R| -> io::Result<E::G1Affine> {
            let mut repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();
            reader.read_exact(repr.as_mut())?;
            if checked {
                repr.into_affine()
            } else {
                repr.into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let read_g2_uncompressed = |reader: &mut R| -> io::Result<E::G2Affine> {
            let mut repr = <E::G2Affine as CurveAffine>::Uncompressed::empty();
            reader.read_exact(repr.as_mut())?;

            if checked {
                repr.into_affine()
            } else {
                repr.into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let mut gp1x = vec![];
        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                gp1x.push(read_g1_uncompressed(&mut reader)?);
            }
        }

        let mut gn1x = vec![];
        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                gn1x.push(read_g1_uncompressed(&mut reader)?);
            }
        }

        let mut gpax = vec![];
        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                gpax.push(read_g1_uncompressed(&mut reader)?);
            }
        }

        let mut gnax = vec![];
        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                gnax.push(read_g1_uncompressed(&mut reader)?);
            }
        }

        let hn1x_len = reader.read_u32::<BigEndian>()? as usize;
        let mut hn1x: HashMap<usize, E::G2Affine> = HashMap::with_capacity(hn1x_len);
        {
            let mut key: usize;
            let mut value: E::G2Affine;
            for _ in 0..hn1x_len {
                key = reader.read_u32::<BigEndian>()? as usize;
                value = read_g2_uncompressed(&mut reader)?;
                hn1x.insert(key, value);
            }
        }

        let hp1x1 = read_g2_uncompressed(&mut reader)?;
        let hpax0 = read_g2_uncompressed(&mut reader)?;
        let hpax1 = read_g2_uncompressed(&mut reader)?;

        let ga = read_g1_uncompressed(&mut reader)?;
        let gx = read_g1_uncompressed(&mut reader)?;
        let prf = UpdateProof::<E> { ga, gx };

        Ok(URS::<E> {
            gp1x,
            gn1x,
            gpax,
            gnax,
            hn1x,
            hp1x1,
            hpax0,
            hpax1,
            prf,
        })
    }

    pub fn write_compressed<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_u32::<BigEndian>(self.gp1x.len() as u32)?;
        for g in &self.gp1x[..] {
            writer.write_all(g.into_compressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.gn1x.len() as u32)?;
        for g in &self.gn1x[..] {
            writer.write_all(g.into_compressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.gpax.len() as u32)?;
        for g in &self.gpax[..] {
            writer.write_all(g.into_compressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.gnax.len() as u32)?;
        for g in &self.gnax[..] {
            writer.write_all(g.into_compressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.hn1x.len() as u32)?;
        for (key, val) in self.hn1x.iter() {
            writer.write_u32::<BigEndian>(*key as u32)?;
            writer.write_all((*val).into_compressed().as_ref())?;
        }

        writer.write_all(self.hp1x1.into_compressed().as_ref())?;
        writer.write_all(self.hpax0.into_compressed().as_ref())?;
        writer.write_all(self.hpax1.into_compressed().as_ref())?;

        writer.write_all(&self.prf.ga.into_compressed().as_ref())?;
        writer.write_all(&self.prf.gx.into_compressed().as_ref())?;

        Ok(())
    }

    pub fn read_compressed<R: Read>(mut reader: R, checked: bool) -> io::Result<Self> {
        let read_g1_compressed = |reader: &mut R| -> io::Result<E::G1Affine> {
            let mut repr = <E::G1Affine as CurveAffine>::Compressed::empty();
            reader.read_exact(repr.as_mut())?;
            if checked {
                repr.into_affine()
            } else {
                repr.into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let read_g2_compressed = |reader: &mut R| -> io::Result<E::G2Affine> {
            let mut repr = <E::G2Affine as CurveAffine>::Compressed::empty();
            reader.read_exact(repr.as_mut())?;

            if checked {
                repr.into_affine()
            } else {
                repr.into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let mut gp1x = vec![];
        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                gp1x.push(read_g1_compressed(&mut reader)?);
            }
        }

        let mut gn1x = vec![];
        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                gn1x.push(read_g1_compressed(&mut reader)?);
            }
        }

        let mut gpax = vec![];
        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                gpax.push(read_g1_compressed(&mut reader)?);
            }
        }

        let mut gnax = vec![];
        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                gnax.push(read_g1_compressed(&mut reader)?);
            }
        }

        let hn1x_len = reader.read_u32::<BigEndian>()? as usize;
        let mut hn1x: HashMap<usize, E::G2Affine> = HashMap::with_capacity(hn1x_len);
        {
            let mut key: usize;
            let mut value: E::G2Affine;
            for _ in 0..hn1x_len {
                key = reader.read_u32::<BigEndian>()? as usize;
                value = read_g2_compressed(&mut reader)?;
                hn1x.insert(key, value);
            }
        }

        let hp1x1 = read_g2_compressed(&mut reader)?;
        let hpax0 = read_g2_compressed(&mut reader)?;
        let hpax1 = read_g2_compressed(&mut reader)?;

        let ga = read_g1_compressed(&mut reader)?;
        let gx = read_g1_compressed(&mut reader)?;
        let prf = UpdateProof::<E> { ga, gx };

        Ok(URS::<E> {
            gp1x,
            gn1x,
            gpax,
            gnax,
            hn1x,
            hp1x1,
            hpax0,
            hpax1,
            prf,
        })
    }
}

impl<E: Engine> PartialEq for UpdateProof<E> {
    fn eq(&self, other: &Self) -> bool {
        if self.ga != other.ga || self.gx != other.gx {
            return false;
        }
        return true;
    }
}

impl<E: Engine> PartialEq for URS<E> {
    fn eq(&self, other: &Self) -> bool {
        if self.gp1x != other.gp1x
            || self.gn1x != other.gn1x
            || self.gpax != other.gpax
            || self.gnax != other.gnax
            //|| self.hp1x != other.hp1x
            || self.hn1x != other.hn1x
            //|| self.hnax != other.hnax
            //|| self.hpax != other.hpax
            || self.prf != other.prf
        {
            return false;
        }
        return true;
    }
}

impl<E: Engine> fmt::Debug for UpdateProof<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "UpdateProof < ga: {:?}, gx {:?} >", self.ga, self.gx)
    }
}

impl<E: Engine> fmt::Debug for URS<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "URS < gp1x: {:?}, gn1x: {:?}, gpax: {:?}, gnax: {:?}, hn1x: {:?}, prf: {:?} >",
            self.gp1x, self.gn1x, self.gpax, self.gnax, self.hn1x, self.prf
        )
    }
}
