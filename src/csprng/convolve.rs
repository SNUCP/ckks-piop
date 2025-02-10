use super::CDTSamplerVarCenter;
use crate::ring::*;

/// ConvolveSampler is a Gaussian sampler for large, variable parameters.
/// It is based on [MW18].
pub struct ConvolveSampler {
    pub base_sampler: CDTSamplerVarCenter,

    pub sigs: Vec<f64>,
    pub weights: Vec<i128>,
    pub s_bar: f64,
}

impl ConvolveSampler {
    pub fn new(max_sigma: f64) -> ConvolveSampler {
        const ETA: f64 = 6.0;

        let depth = max_sigma.log2().log2().ceil() as usize;

        let mut z = vec![0; depth + 1];
        let mut s = vec![0.0; depth + 1];
        s[0] = 4.0 * f64::sqrt(2.0) * ETA;
        for i in 1..=depth {
            z[i] = (s[i - 1] / (f64::sqrt(2.0) * ETA)).floor() as i128;
            s[i] = f64::sqrt((z[i] * z[i] + (z[i] - 1) * (z[i] - 1)) as f64) * s[i - 1];
        }

        let base_sampler = CDTSamplerVarCenter::new(s[0]);

        let mut sig_bar = 0.0;
        for i in 0..depth {
            sig_bar += f64::powi((1 << base_sampler.b_log) as f64, -2 * i as i32);
        }
        sig_bar *= s[0];

        ConvolveSampler {
            base_sampler: base_sampler,

            sigs: s,
            weights: z,
            s_bar: sig_bar,
        }
    }

    /// Algorithm SampleI from [MW18].
    pub fn sample_i(&mut self, i: usize) -> i128 {
        if i == 0 {
            return self.base_sampler.base_samplers[0].sample() as i128;
        }

        let x1 = self.sample_i(i - 1);
        let x2 = self.sample_i(i - 1);

        let z1 = self.weights[i];
        let z2 = i128::max(1, z1 - 1);

        return z1 * x1 + z2 * x2;
    }

    /// Returns a sample from the Gaussian distribution.
    pub fn sample(&mut self, c: f64, s: f64) -> i64 {
        let x = self.sample_i(self.sigs.len() - 1);
        let k = f64::sqrt(s * s - self.s_bar * self.s_bar) / self.sigs[self.sigs.len() - 1];

        let cc = c + k * (x as f64);
        return self.base_sampler.sample(cc);
    }

    /// Returns a sample from the Gaussian distribution over a coset c + Z.
    pub fn sample_coset(&mut self, c: f64, s: f64) -> f64 {
        return c + (self.sample(-c, s) as f64);
    }

    /// Samples a polynomial with coefficients from the Gaussian distribution.
    /// Output polynomial is in NTT domain.
    pub fn sample_poly_assign(&mut self, ring: &Ring, s: f64, pout: &mut Poly) {
        pout.is_ntt = false;

        for i in 0..ring.degree {
            let cc = self.sample(0.0, s);
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
