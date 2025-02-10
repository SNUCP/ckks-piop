use csprng::UniformSampler;
use rug::{Assign, Integer};

use crate::*;

pub struct Encoder<'a> {
    pub params: &'a Parameters,
    pub uniform_sampler: UniformSampler,
    pub transformer_n: CyclicTransformer,
    pub transformer_2n: CyclicTransformer,
    pub embedding_n: usize,
}

impl<'a> Encoder<'a> {
    pub fn new(params: &'a Parameters) -> Self {
        let root_2n = gen_root_of_unity(2 * params.rlwe.n, &params.rlwe.q);
        let root_n = root_2n.clone() * &root_2n;

        let transformer_n =
            CyclicTransformer::new_with_root(params.rlwe.n, &params.rlwe.q, &root_n);
        let transformer_2n =
            CyclicTransformer::new_with_root(2 * params.rlwe.n, &params.rlwe.q, &root_2n);

        Encoder {
            params: params,
            uniform_sampler: UniformSampler::new(),
            transformer_n: transformer_n,
            transformer_2n: transformer_2n,
            embedding_n: params.embedding_n,
        }
    }

    /// Encodes w. w should be of length N.
    pub fn encode(&self, w: &[Integer]) -> BigPoly {
        let mut w_out = BigPoly::new(self.embedding_n, false);
        self.encode_assign(w, &mut w_out);
        return w_out;
    }

    /// Encodes w to w_out.
    pub fn encode_assign(&self, w: &[Integer], w_out: &mut BigPoly) {
        for i in 0..self.params.rlwe.n {
            w_out.coeffs[i].assign(&w[i]);
        }

        self.transformer_n
            .intt(&mut w_out.coeffs[0..self.params.rlwe.n]);

        for i in self.params.rlwe.n..self.embedding_n {
            w_out.coeffs[i] = Integer::ZERO;
        }
        w_out.is_ntt = false;
    }

    /// Encodes w with randomization. w should be of length N.
    pub fn encode_randomize(&mut self, w: &[Integer]) -> BigPoly {
        let mut w_out = BigPoly::new(self.embedding_n, false);
        self.encode_randomize_assign(w, &mut w_out);
        return w_out;
    }

    /// Encodes w with randomization to w_out.
    pub fn encode_randomize_assign(&mut self, w: &[Integer], w_out: &mut BigPoly) {
        for i in 0..self.params.rlwe.n {
            w_out.coeffs[2 * i].assign(&w[i]);
            w_out.coeffs[2 * i + 1] = self
                .uniform_sampler
                .sample_range_bigint(&self.params.rlwe.q);
        }

        self.transformer_2n
            .intt(&mut w_out.coeffs[0..2 * self.params.rlwe.n]);

        for i in 2 * self.params.rlwe.n..self.embedding_n {
            w_out.coeffs[i] = Integer::ZERO;
        }
        w_out.is_ntt = false;
    }
}
