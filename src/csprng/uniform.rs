use crate::ring::*;
use rand::prelude::*;
use rug::{Complete, Integer};
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake128, Shake128Reader,
};

pub struct UniformSampler {
    pub xof: Shake128Reader,
    pub buf: [u8; 8],
}

impl UniformSampler {
    /// Create a new uniform sampler.
    pub fn new() -> UniformSampler {
        let mut seed = [0u8; 32];

        let mut rng = StdRng::from_entropy();
        rng.fill_bytes(&mut seed);

        let mut hasher = Shake128::default();
        hasher.update(&seed);
        let xof = hasher.finalize_xof();

        UniformSampler {
            xof: xof,
            buf: [0u8; 8],
        }
    }

    /// Create a new uniform sampler with seed.
    pub fn new_with_seed(seed: &[u8]) -> UniformSampler {
        let mut hasher = Shake128::default();
        hasher.update(seed);
        let xof = hasher.finalize_xof();

        UniformSampler {
            xof: xof,
            buf: [0u8; 8],
        }
    }

    /// Samples a random u64 value.
    pub fn sample_u64(&mut self) -> u64 {
        self.xof.read(&mut self.buf);
        u64::from_le_bytes(self.buf)
    }

    /// Samples a random i64 value.
    pub fn sample_i64(&mut self) -> i64 {
        self.xof.read(&mut self.buf);
        i64::from_le_bytes(self.buf)
    }

    /// Samples bytes.
    pub fn sample_bytes(&mut self, buf: &mut [u8]) {
        self.xof.read(buf);
    }

    /// Samples random u64 between [0, n).
    pub fn sample_range(&mut self, n: u64) -> u64 {
        let bound = u64::MAX - (u64::MAX % n);
        loop {
            let x = self.sample_u64();
            if x < bound {
                return x % n;
            }
        }
    }

    /// Samples random Integer between [0, n).
    pub fn sample_range_bigint(&mut self, n: &Integer) -> Integer {
        let bytes = n.significant_digits::<u8>();
        let max = Integer::from(1) << (bytes * 8);
        let max_mod_n = max.modulo_ref(n).complete();
        let bound = max - max_mod_n;
        let mut buf = vec![0u8; bytes];
        loop {
            self.sample_bytes(&mut buf);
            let mut x = Integer::from_digits(&buf, rug::integer::Order::Lsf);
            if x <= bound {
                x.modulo_mut(n);
                return x;
            }
        }
    }

    /// Samples a random f64 value between 0 and 1.
    pub fn sample_f64(&mut self) -> f64 {
        self.sample_u64() as f64 / (u64::MAX as f64)
    }

    /// Samples a random polynomial.
    /// Output polynomial is in NTT domain.
    pub fn sample_poly(&mut self, ring: &Ring) -> Poly {
        let mut pout = ring.new_ntt_poly();
        self.sample_poly_assign(ring, &mut pout);
        return pout;
    }

    /// Samples a random polynomial.
    pub fn sample_poly_assign(&mut self, ring: &Ring, pout: &mut Poly) {
        for (i, &q) in ring.moduli.iter().enumerate() {
            for j in 0..pout.coeffs[i].len() {
                pout.coeffs[i][j] = self.sample_range(q);
            }
        }
    }
}
