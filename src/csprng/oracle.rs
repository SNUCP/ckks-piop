use crate::ring::*;
use rug::{Complete, Integer};
use sha3::{
    digest::{ExtendableOutput, Reset, Update, XofReader},
    Shake128, Shake128Reader,
};

pub struct Oracle {
    hasher: Shake128,
    xof: Shake128Reader,
}

impl Oracle {
    /// Create a new uniform sampler.
    pub fn new() -> Oracle {
        Oracle {
            hasher: Shake128::default(),
            xof: Shake128::default().finalize_xof(),
        }
    }

    /// Writes a bigint value to random oracle.
    pub fn write_bigint(&mut self, x: &Integer) {
        let buf = x.to_digits::<u8>(rug::integer::Order::Lsf);
        self.hasher.update(&buf);
    }

    /// Writes a polynomial to random oracle.
    pub fn write_poly(&mut self, p: &Poly) {
        for i in 0..p.coeffs.len() {
            for j in 0..p.coeffs[i].len() {
                self.hasher.update(&p.coeffs[i][j].to_be_bytes());
            }
        }
    }

    /// Finalizes the random oracle.
    pub fn finalize(&mut self) {
        self.xof = self.hasher.clone().finalize_xof();
        self.hasher.reset();
    }

    /// Reads a byte vector.
    pub fn read_bytes(&mut self, buf: &mut [u8]) {
        self.xof.read(buf);
    }

    /// Reads a bigint value smaller than n.
    pub fn read_range_bigint(&mut self, n: &Integer) -> Integer {
        let bytes = n.significant_digits::<u8>();
        let max = Integer::from(1) << (bytes * 8);
        let max_mod_n = max.modulo_ref(n).complete();
        let bound = max - max_mod_n;
        let mut buf = vec![0u8; bytes];
        loop {
            self.read_bytes(&mut buf);
            let mut x = Integer::from_digits(&buf, rug::integer::Order::Lsf);
            if x <= bound {
                x.modulo_mut(n);
                return x;
            }
        }
    }

    /// Reads a polynomial.
    /// Output polynomial is in NTT domain.
    pub fn read_poly(&mut self, ring: &Ring) -> Poly {
        let mut pout = ring.new_ntt_poly();
        self.read_poly_assign(ring, &mut pout);
        return pout;
    }

    /// Reads a polynomial.
    pub fn read_poly_assign(&mut self, ring: &Ring, pout: &mut Poly) {
        let mut buff = [0u8; 8];
        for i in 0..pout.coeffs.len() {
            let q = ring.moduli[i];
            let bound = u64::MAX - (u64::MAX % q);
            for j in 0..pout.coeffs[i].len() {
                loop {
                    self.xof.read(&mut buff);
                    let x = u64::from_be_bytes(buff);
                    if x < bound {
                        pout.coeffs[i][j] = x % q;
                        break;
                    }
                }
            }
        }
    }

    /// Reads a monomial.
    /// Output polynomial is in NTT domain.
    pub fn read_monomial(&mut self, ring: &Ring) -> Poly {
        let mut mout = ring.new_poly();
        self.read_monomial_assign(ring, &mut mout);
        return mout;
    }

    /// Reads a monomial.
    /// Output polynomial is in NTT domain.
    pub fn read_monomial_assign(&mut self, ring: &Ring, mout: &mut Poly) {
        mout.clear();

        let mut buff = [0u8; 8];
        let bound = usize::MAX - (usize::MAX % (2 * ring.degree));
        loop {
            self.xof.read(&mut buff);
            let mut x = usize::from_be_bytes(buff);

            if x < bound {
                x %= 2 * ring.degree;

                let s = x & 1;
                if s == 0 {
                    for i in 0..mout.coeffs.len() {
                        mout.coeffs[i][x >> 1] = 1
                    }
                } else {
                    for i in 0..mout.coeffs.len() {
                        mout.coeffs[i][x >> 1] = ring.moduli[i] - 1
                    }
                }

                mout.is_ntt = false;
                ring.ntt(mout);
                return;
            }
        }
    }
}
