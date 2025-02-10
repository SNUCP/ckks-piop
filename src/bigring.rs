use crate::*;
use rug::{Assign, Complete, Integer};

#[derive(Clone, Debug)]
pub struct BigMultiVariatePoly {
    pub coeffs: Vec<(Integer, Vec<usize>)>,
    pub max_degree: usize,
}

#[derive(Clone, Debug)]
pub struct PolyMultiVariatePoly {
    pub coeffs: Vec<(BigPoly, Vec<usize>)>,
    pub max_degree: usize,
}

/// Unlike other polynomial types, BigPoly is not in a quotient ring.
/// However, for fast arithmetic, it is embedded in a large enough quotient ring.
/// The degree of the polynmial represents the actual degree, so it may differ from the length of coefficients.
#[derive(Clone, Debug)]
pub struct BigPoly {
    pub coeffs: Vec<Integer>,
    pub is_ntt: bool,
}

impl BigPoly {
    pub fn new(embedding_degree: usize, is_ntt: bool) -> Self {
        Self {
            coeffs: vec![Integer::ZERO; embedding_degree],
            is_ntt: is_ntt,
        }
    }
}

/// Similar with BigPoly, BigRing is not in a quotient ring.
/// However, for fast arithmetic, it is embedded in a large enough quotient ring.
pub struct BigRing {
    pub embedding_degree: usize,
    pub modulus: Integer,
    pub transformer: CyclicTransformer,
}

impl BigRing {
    pub fn new(embedding_degree: usize, modulus: &Integer) -> Self {
        Self {
            embedding_degree: embedding_degree,
            modulus: modulus.clone(),
            transformer: CyclicTransformer::new(embedding_degree, modulus),
        }
    }

    /// Create a new polynomial with the given degree and modulus.
    /// The polynomial is not in NTT form.
    pub fn new_poly(&self) -> BigPoly {
        BigPoly {
            coeffs: vec![Integer::ZERO; self.embedding_degree],
            is_ntt: false,
        }
    }

    /// Create a new polynomial with the given degree and modulus.
    /// The polynomial is in NTT form.
    pub fn new_ntt_poly(&self) -> BigPoly {
        BigPoly {
            coeffs: vec![Integer::ZERO; self.embedding_degree],
            is_ntt: true,
        }
    }

    /// Applies NTT and returns the result.
    pub fn ntt(&self, poly: &BigPoly) -> BigPoly {
        if poly.is_ntt {
            panic!("Polynomial is already in NTT form.");
        }

        let mut pout = BigPoly::new(self.embedding_degree, true);
        self.ntt_assign(poly, &mut pout);
        return pout;
    }

    /// Applies NTT and assigns the result to pout.
    pub fn ntt_assign(&self, poly: &BigPoly, pout: &mut BigPoly) {
        if poly.is_ntt {
            panic!("Polynomial is already in NTT form.");
        }

        pout.coeffs.clone_from(&poly.coeffs);
        self.transformer.ntt(&mut pout.coeffs);
        pout.is_ntt = true;
    }

    /// Applies NTT to the given polynomial.
    pub fn ntt_inplace(&self, poly: &mut BigPoly) {
        if poly.is_ntt {
            panic!("Polynomial is already in NTT form.");
        }

        self.transformer.ntt(&mut poly.coeffs);
        poly.is_ntt = true;
    }

    /// Applies Inverse NTT and returns the result.
    pub fn intt(&self, poly: &BigPoly) -> BigPoly {
        if !poly.is_ntt {
            panic!("Polynomial is not in NTT form.");
        }

        let mut pout = BigPoly::new(self.embedding_degree, false);
        self.intt_assign(poly, &mut pout);
        return pout;
    }

    /// Applies Inverse NTT and assigns the result to pout.
    pub fn intt_assign(&self, poly: &BigPoly, pout: &mut BigPoly) {
        if !poly.is_ntt {
            panic!("Polynomial is not in NTT form.");
        }

        pout.coeffs.clone_from(&poly.coeffs);
        self.transformer.intt(&mut pout.coeffs);
        pout.is_ntt = false;
    }

    /// Applies Inverse NTT to the given polynomial.
    pub fn intt_inplace(&self, poly: &mut BigPoly) {
        if !poly.is_ntt {
            panic!("Polynomial is not in NTT form.");
        }

        self.transformer.intt(&mut poly.coeffs);
        poly.is_ntt = false;
    }

    /// Adds p1 and p2, and returns the result.
    pub fn add(&self, p1: &BigPoly, p2: &BigPoly) -> BigPoly {
        if p1.is_ntt != p2.is_ntt {
            panic!("Polynomials must be in the same form.");
        }

        let mut p_out = BigPoly::new(self.embedding_degree, p1.is_ntt);
        self.add_assign(p1, p2, &mut p_out);
        return p_out;
    }

    /// Adds p1 and p2, and assigns the result to p_out.
    pub fn add_assign(&self, p1: &BigPoly, p2: &BigPoly, p_out: &mut BigPoly) {
        if p1.is_ntt != p2.is_ntt {
            panic!("Polynomials must be in the same form.");
        }

        for i in 0..self.embedding_degree {
            p_out.coeffs[i].assign(&p1.coeffs[i]);
            p_out.coeffs[i] += &p2.coeffs[i];
            if p_out.coeffs[i] >= self.modulus {
                p_out.coeffs[i] -= &self.modulus;
            }
        }
    }

    /// Adds p to pout.
    pub fn add_inplace(&self, p: &BigPoly, pout: &mut BigPoly) {
        if p.is_ntt != pout.is_ntt {
            panic!("Polynomials must be in the same form.");
        }

        for i in 0..self.embedding_degree {
            pout.coeffs[i] += &p.coeffs[i];
            pout.coeffs[i].modulo_mut(&self.modulus);
        }
    }

    /// Subtracts p2 from p1, and returns the result.
    pub fn sub(&self, p1: &BigPoly, p2: &BigPoly) -> BigPoly {
        if p1.is_ntt != p2.is_ntt {
            panic!("Polynomials must be in the same form.");
        }

        let mut p_out = BigPoly::new(self.embedding_degree, p1.is_ntt);
        self.sub_assign(p1, p2, &mut p_out);
        return p_out;
    }

    /// Subtracts p2 from p1, and assigns the result to p_out.
    pub fn sub_assign(&self, p1: &BigPoly, p2: &BigPoly, p_out: &mut BigPoly) {
        if p1.is_ntt != p2.is_ntt {
            panic!("Polynomials must be in the same form.");
        }

        for i in 0..self.embedding_degree {
            p_out.coeffs[i].assign(&p1.coeffs[i]);
            p_out.coeffs[i] -= &p2.coeffs[i];
            if p_out.coeffs[i].is_negative() {
                p_out.coeffs[i] += &self.modulus;
            }
        }
    }

    /// Subtracts p from pout.
    pub fn sub_inplace(&self, p: &BigPoly, pout: &mut BigPoly) {
        if p.is_ntt != pout.is_ntt {
            panic!("Polynomials must be in the same form.");
        }

        for i in 0..self.embedding_degree {
            pout.coeffs[i] -= &p.coeffs[i];
            if pout.coeffs[i].is_negative() {
                pout.coeffs[i] += &self.modulus;
            }
        }
    }

    /// Multiplies p1, c and returns it.
    pub fn mul_const(&self, p1: &BigPoly, c: &Integer) -> BigPoly {
        let mut pout = self.new_poly();
        self.mul_const_assign(p1, c, &mut pout);
        return pout;
    }

    /// Multiplies p1, c and writes it to pout.
    pub fn mul_const_assign(&self, p1: &BigPoly, c: &Integer, pout: &mut BigPoly) {
        if p1.is_ntt != pout.is_ntt {
            panic!("Polynomials must be in the same form.");
        }

        for i in 0..self.embedding_degree {
            pout.coeffs[i].assign(&p1.coeffs[i]);
            pout.coeffs[i] *= c;
            pout.coeffs[i].modulo_mut(&self.modulus);
        }
    }

    /// Multiplies p by c.
    pub fn mul_const_inplace(&self, c: &Integer, pout: &mut BigPoly) {
        for i in 0..self.embedding_degree {
            pout.coeffs[i] *= c;
            pout.coeffs[i].modulo_mut(&self.modulus);
        }
    }

    /// Multiplies p1, p2 and returns it.
    /// The input polynomials are assumed to be in NTT form.
    /// The output polynomial is in NTT form.
    pub fn mul(&self, p1: &BigPoly, p2: &BigPoly) -> BigPoly {
        let mut pout = self.new_ntt_poly();
        self.mul_assign(p1, p2, &mut pout);
        return pout;
    }

    /// Multiplies p1, p2 and writes it to pout.
    /// The input polynomials are assumed to be in NTT form.
    /// The output polynomial is in NTT form.
    pub fn mul_assign(&self, p1: &BigPoly, p2: &BigPoly, pout: &mut BigPoly) {
        if !(p1.is_ntt && p2.is_ntt && pout.is_ntt) {
            panic!("Polynomials must be in NTT form.");
        }

        for i in 0..self.embedding_degree {
            pout.coeffs[i].assign(&p1.coeffs[i]);
            pout.coeffs[i] *= &p2.coeffs[i];
            pout.coeffs[i].modulo_mut(&self.modulus);
        }
    }

    /// Multiplies p to pout.
    /// The input polynomials are assumed to be in NTT form.
    /// The output polynomial is in NTT form.
    pub fn mul_inplace(&self, p: &BigPoly, pout: &mut BigPoly) {
        if !(p.is_ntt && pout.is_ntt) {
            panic!("Polynomials must be in NTT form.");
        }

        for i in 0..self.embedding_degree {
            pout.coeffs[i] *= &p.coeffs[i];
            pout.coeffs[i].modulo_mut(&self.modulus);
        }
    }

    /// Multiplies p1, p2 and adds it to pout.
    /// The input polynomials are assumed to be in NTT form.
    /// The output polynomial is in NTT form.
    pub fn mul_add_inplace(&self, p1: &BigPoly, p2: &BigPoly, pout: &mut BigPoly) {
        if !(p1.is_ntt && p2.is_ntt && pout.is_ntt) {
            panic!("Polynomials must be in NTT form.");
        }

        let mut buf = Integer::ZERO;
        for i in 0..self.embedding_degree {
            buf.assign(&p1.coeffs[i]);
            buf *= &p2.coeffs[i];
            pout.coeffs[i] += &buf;
            pout.coeffs[i].modulo_mut(&self.modulus);
        }
    }

    /// Multiplies p1, p2 and subracts it from pout.
    /// The input polynomials are assumed to be in NTT form.
    /// The output polynomial is in NTT form.
    pub fn mul_sub_inplace(&self, p1: &BigPoly, p2: &BigPoly, pout: &mut BigPoly) {
        if !(p1.is_ntt && p2.is_ntt && pout.is_ntt) {
            panic!("Polynomials must be in NTT form.");
        }

        let mut buf = Integer::ZERO;
        for i in 0..self.embedding_degree {
            buf.assign(&p1.coeffs[i]);
            buf *= &p2.coeffs[i];
            pout.coeffs[i] -= &buf;
            pout.coeffs[i].modulo_mut(&self.modulus);
        }
    }

    /// Computes the quotient and remainder by the zero polynomial z_H = X^z - 1.
    pub fn quo_rem_zero(&self, p: &BigPoly, z: usize) -> (BigPoly, BigPoly) {
        let mut q = self.new_poly();
        let mut r = self.new_poly();

        self.quo_rem_zero_assign(p, z, &mut q, &mut r);

        return (q, r);
    }

    /// Computes the quotient and remainder by the zero polynomial z_H = X^z - 1, and assigns them to q and r.
    pub fn quo_rem_zero_assign(&self, p: &BigPoly, z: usize, q: &mut BigPoly, r: &mut BigPoly) {
        if z > self.embedding_degree {
            panic!("z must be less than the degree of the polynomial.");
        }

        if p.is_ntt {
            panic!("Polynomial must not be in NTT form.");
        }

        for i in 0..self.embedding_degree {
            q.coeffs[i] = Integer::ZERO;
            r.coeffs[i].assign(&p.coeffs[i]);
        }
        q.is_ntt = false;
        r.is_ntt = false;

        let mut c = Integer::ZERO;
        for i in (z..self.embedding_degree).rev() {
            c.assign(&r.coeffs[i]);
            // Current leading term: c * X^i
            // Add c * X^(i - z) to q
            q.coeffs[i - z] += &c;
            if q.coeffs[i - z] >= self.modulus {
                q.coeffs[i - z] -= &self.modulus;
            }

            // Subtract c * X^i - c * X^(i - z) from r
            r.coeffs[i] -= &c;
            if r.coeffs[i].is_negative() {
                r.coeffs[i] += &self.modulus;
            }
            r.coeffs[i - z] += &c;
            if r.coeffs[i - z] >= self.modulus {
                r.coeffs[i - z] -= &self.modulus;
            }
        }
    }

    /// Evaluate a polynomial at the given point, and return the result.
    pub fn evaluate(&self, p: &BigPoly, x: &Integer) -> Integer {
        if p.is_ntt {
            panic!("Polynomial must not be in NTT form.");
        }

        let mut y = Integer::ZERO;
        for i in (0..self.embedding_degree).rev() {
            y *= x;
            y += &p.coeffs[i];
            y.modulo_mut(&self.modulus);
        }

        return y;
    }

    /// Evaluates a multivariate polynomial at the given point, and returns the result.
    pub fn evaluate_multivariate(&self, p: &BigMultiVariatePoly, xi: &[Integer]) -> Integer {
        let mut y = Integer::ZERO;

        let mut buf = Integer::ZERO;
        for (c, exp) in &p.coeffs {
            buf.assign(c);
            for (i, &e) in exp.iter().enumerate() {
                buf *= xi[i]
                    .pow_mod_ref(&Integer::from(e), &self.modulus)
                    .unwrap()
                    .complete();
            }
            y += &buf;
            y.modulo_mut(&self.modulus);
        }

        return y;
    }

    /// Evaluates a multivariate polynomial at the given point, and returns the result.
    pub fn evaluate_multivariate_poly(&self, p: &BigMultiVariatePoly, xi: &[BigPoly]) -> BigPoly {
        let mut pout = self.new_ntt_poly();
        self.evaluate_multivariate_poly_assign(p, xi, &mut pout);
        return pout;
    }

    /// Evaluates a multivariate polynomial at the given point, and assigns the result to pout.
    pub fn evaluate_multivariate_poly_assign(
        &self,
        p: &BigMultiVariatePoly,
        xi: &[BigPoly],
        pout: &mut BigPoly,
    ) {
        if !pout.is_ntt {
            panic!("Output polynomial must be in NTT form.");
        }

        for i in 0..xi.len() {
            if !xi[i].is_ntt {
                panic!("Input polynomials must be in NTT form.");
            }
        }

        for i in 0..self.embedding_degree {
            pout.coeffs[i] = Integer::ZERO;
        }

        let mut buf = self.new_ntt_poly();
        for (c, exp) in &p.coeffs {
            for i in 0..self.embedding_degree {
                buf.coeffs[i].assign(c);
            }

            for (i, &e) in exp.iter().enumerate() {
                for _ in 0..e {
                    self.mul_inplace(&xi[i], &mut buf);
                }
            }

            for i in 0..self.embedding_degree {
                pout.coeffs[i] += &buf.coeffs[i];
                if pout.coeffs[i] >= self.modulus {
                    pout.coeffs[i] -= &self.modulus;
                }
            }
        }
    }

    /// Evaluates a multivariate polynomial at the given point, and returns the result.
    pub fn evaluate_poly_multivariate_poly(
        &self,
        p: &PolyMultiVariatePoly,
        xi: &[&BigPoly],
    ) -> BigPoly {
        let mut pout = self.new_ntt_poly();
        self.evaluate_poly_multivariate_poly_assign(p, xi, &mut pout);
        return pout;
    }

    /// Evaluates a multivariate polynomial at the given point, and assigns the result to pout.
    pub fn evaluate_poly_multivariate_poly_assign(
        &self,
        p: &PolyMultiVariatePoly,
        xi: &[&BigPoly],
        pout: &mut BigPoly,
    ) {
        if !pout.is_ntt {
            panic!("Output polynomial must be in NTT form.");
        }

        for i in 0..xi.len() {
            if !xi[i].is_ntt {
                panic!("Input polynomials must be in NTT form.");
            }
        }

        for i in 0..self.embedding_degree {
            pout.coeffs[i] = Integer::ZERO;
        }

        let mut buf = self.new_ntt_poly();
        for (c, exp) in &p.coeffs {
            if !c.is_ntt {
                panic!("Input polynomials must be in NTT form.");
            }

            for i in 0..self.embedding_degree {
                buf.coeffs[i].assign(&c.coeffs[i]);
            }

            for (i, &e) in exp.iter().enumerate() {
                for _ in 0..e {
                    self.mul_inplace(&xi[i], &mut buf);
                }
            }

            for i in 0..self.embedding_degree {
                pout.coeffs[i] += &buf.coeffs[i];
                if pout.coeffs[i] >= self.modulus {
                    pout.coeffs[i] -= &self.modulus;
                }
            }
        }
    }
}
