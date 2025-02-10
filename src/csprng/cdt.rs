use std::f64::consts::PI;

use super::UniformSampler;
use crate::ring::*;

/// CDTSampler is a Gaussian sampler for small, fixed parameters.
/// Additionally, it is used as a base sampler for ConvSampler.
pub struct CDTSampler {
    pub base_sampler: UniformSampler,

    pub c: f64,
    pub s: f64,

    pub table: Vec<u64>,

    pub tailcut_low: i64,
    pub tailcut_high: i64,
}

impl CDTSampler {
    pub fn new(center: f64, sigma: f64) -> CDTSampler {
        let base_sampler = UniformSampler::new();

        let tailcut_low = (center - 6.0 * sigma).round() as i64;
        let tailcut_high = (center + 6.0 * sigma).round() as i64;
        let table_size = (tailcut_high - tailcut_low + 1) as usize;

        let mut table_f64 = Vec::with_capacity(table_size);
        let mut table_u64 = Vec::with_capacity(table_size);
        let mut sum = 0.0;
        for x in tailcut_low..=tailcut_high {
            let xf = x as f64;
            let rho = f64::exp(-PI * (xf - center) * (xf - center) / (sigma * sigma));
            sum += rho;
            table_f64.push(sum);
        }

        for i in 0..table_size {
            let rho_normalized = table_f64[i] / sum;
            if rho_normalized >= 1.0 {
                table_u64.push(u64::MAX);
            } else {
                table_u64.push((rho_normalized * (u64::MAX as f64)) as u64);
            }
        }

        CDTSampler {
            base_sampler: base_sampler,
            c: center,
            s: sigma,

            table: table_u64,
            tailcut_low,
            tailcut_high,
        }
    }

    /// Returns a sample from the Gaussian distribution.
    pub fn sample(&mut self) -> i64 {
        let r = self.base_sampler.sample_u64();

        let x = self.table.binary_search(&r).unwrap_or_else(|x| x - 1);
        return x as i64 + self.tailcut_low;
    }

    /// Samples a polynomial with coefficients from the Gaussian distribution.
    /// Output polynomial is in NTT domain.
    pub fn sample_poly_assign(&mut self, ring: &Ring, pout: &mut Poly) {
        pout.is_ntt = false;

        for i in 0..ring.degree {
            let cc = self.sample();
            if cc < 0 {
                for j in 0..ring.moduli.len() {
                    pout.coeffs[j][i] = (cc + (ring.moduli[j] as i64)) as u64;
                }
            } else {
                for j in 0..ring.moduli.len() {
                    pout.coeffs[j][i] = cc as u64;
                }
            }
        }
        ring.ntt(pout);
    }
}

/// CDTSamplerVarCenter is a variant of CDTSampler with variable center and fixed sigma.
/// This is possible by using SampleC algorithm from [MW18].
pub struct CDTSamplerVarCenter {
    pub base_samplers: Vec<CDTSampler>,

    pub b_log: u64,
    pub k: u64,
    pub prec_log: u64,
}

impl CDTSamplerVarCenter {
    pub fn new(sigma: f64) -> CDTSamplerVarCenter {
        let b_log = 10;
        let k = 3;

        let mut base_samplers = Vec::new();
        for i in 0..(1 << b_log) {
            base_samplers.push(CDTSampler::new((i as f64) / f64::exp2(b_log as f64), sigma));
        }

        CDTSamplerVarCenter {
            base_samplers: base_samplers,

            b_log: b_log,
            k: k,
            prec_log: b_log * k,
        }
    }

    /// Returns a sample from the Gaussian distribution.
    pub fn sample(&mut self, c: f64) -> i64 {
        let ci = c.floor() as i64;
        let c = c - c.floor(); // c is now always in [0, 1).

        let f64_prec_log = 52;
        let tail_prec_log = f64_prec_log - self.prec_log;

        let cx = (c * f64::exp2(f64_prec_log as f64)) as u64;
        let cmsb = cx >> tail_prec_log;
        let r = self.base_samplers[0].base_sampler.sample_u64();
        for i in (0..tail_prec_log).rev() {
            let b = (r >> i) & 1;
            let cbit = (cx >> i) & 1;
            if b > cbit {
                return self.sample_c(cmsb) + ci;
            }
            if b < cbit {
                return self.sample_c(cmsb + 1) + ci;
            }
        }
        return self.sample_c(cmsb + 1) + ci;
    }

    /// Samples from Gaussian distribution with center c / 2^30.
    fn sample_c(&mut self, c: u64) -> i64 {
        let mut x = c as i64;
        let mask = (1 << self.b_log) - 1;
        for _ in 0..self.k {
            let mut g = self.base_samplers[(x & mask) as usize].sample();
            if (x & mask) > 0 && x < 0 {
                g -= 1;
            }
            x >>= self.b_log;
            x += g;
        }
        return x;
    }

    /// Returns a sample from the Gaussian distribution over a coset c + Z.
    pub fn sample_coset(&mut self, center: f64) -> f64 {
        return center + (self.sample(-center) as f64);
    }
}
