use rug::Float;
use rug::Integer;

use super::*;
use crate::csprng::*;
use crate::ring::*;

#[derive(Clone)]
pub struct PolynomialCommitment {
    pub h: Vec<Vec<Poly>>,
    pub eta: Vec<Vec<Poly>>,
    pub h_commit: Vec<Vec<Poly>>,
}

#[derive(Clone)]
pub struct EvaluationProof {
    pub e: Vec<Poly>,
    pub eps: Vec<Poly>,
    pub y_big: Integer,
}

#[derive(Clone)]
pub struct OpenProof {
    pub ch: Vec<Vec<Poly>>,
    pub t: Vec<Vec<Poly>>,
    pub tau: Vec<Vec<Poly>>,
}

pub struct PolynomialProver<'a> {
    pub params: &'a Parameters,
    pub encoder: Encoder<'a>,
    pub uniform_sampler: UniformSampler,

    pub s1_encoder: EncoderRandSmall<'a>,
    pub s2_encoder: EncoderRandLarge<'a>,
    pub s3_encoder: EncoderRandLarge<'a>,

    pub sig1_sampler: CDTSampler,
    pub sig2_sampler: ConvolveSampler,
    pub sig3_sampler: ConvolveSampler,

    pub oracle: Oracle,

    pub key: &'a CommitKey,

    pub committer: Committer<'a>,
}

impl<'a> PolynomialProver<'a> {
    /// Create a new R1CSProver.
    pub fn new(params: &'a Parameters, key: &'a CommitKey) -> PolynomialProver<'a> {
        PolynomialProver {
            params: params,
            encoder: Encoder::new(params),
            uniform_sampler: UniformSampler::new(),
            oracle: Oracle::new(),

            s1_encoder: EncoderRandSmall::new(params, params.s1),
            s2_encoder: EncoderRandLarge::new(params, (params.N as f64).sqrt() * params.s2),
            s3_encoder: EncoderRandLarge::new(params, (params.N as f64).sqrt() * params.s3),

            sig1_sampler: CDTSampler::new(0.0, params.sig1),
            sig2_sampler: ConvolveSampler::new((params.N as f64).sqrt() * params.sig2),
            sig3_sampler: ConvolveSampler::new((params.N as f64).sqrt() * params.sig3),

            key: key,

            committer: Committer::new(params, key),
        }
    }

    pub fn commit(&mut self, h_raw: &[Integer]) -> PolynomialCommitment {
        // assert_eq!(h_raw.len(), self.params.m * self.params.n);
        if h_raw.len() % self.params.n != 0 {
            panic!("Invalid input size");
        }

        let m = h_raw.len() / self.params.n;

        let s3 = ((m + 2) as f64).sqrt() * self.params.s3;
        let sig3 = ((m + 2) as f64).sqrt() * self.params.sig3;

        let mut b0 = vec![Integer::ZERO; self.params.n];
        let mut b1 = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n - 1 {
            b0[i] = self.uniform_sampler.sample_range_bigint(&self.params.p);
            b1[i + 1] = self.params.p.clone() - &b0[i];
        }

        let mut h = vec![vec![self.params.ringq.new_poly(); self.params.l]; m + 2];
        for (i, h_raw_chunk) in h_raw.chunks_exact(self.params.n).enumerate() {
            self.s1_encoder
                .encode_randomized_chunk_assign(h_raw_chunk, &mut h[i]);
        }
        self.s1_encoder
            .encode_randomized_chunk_assign(&b0, &mut h[m]);
        self.s3_encoder
            .encode_randomized_chunk_assign(&b1, s3, &mut h[m + 1]);

        let mut eta =
            vec![vec![self.params.ringq.new_poly(); self.params.mu + self.params.nu]; m + 2];
        for i in 0..m + 1 {
            for j in 0..self.params.mu + self.params.nu {
                self.sig1_sampler
                    .sample_poly_assign(&self.params.ringq, &mut eta[i][j]);
            }
        }
        for j in 0..self.params.mu + self.params.nu {
            self.sig3_sampler
                .sample_poly_assign(&self.params.ringq, sig3, &mut eta[m + 1][j]);
        }
        let mut h_commit = vec![vec![self.params.ringq.new_ntt_poly(); self.params.mu]; m + 2];
        for i in 0..m + 2 {
            self.committer
                .commit_assign(&h[i], &eta[i], &mut h_commit[i]);
        }

        return PolynomialCommitment {
            h: h,
            eta: eta,
            h_commit: h_commit,
        };
    }

    pub fn evaluate(&mut self, x_big: &Integer, pc: &PolynomialCommitment) -> EvaluationProof {
        let m = pc.h.len() - 2;

        let x = self.encoder.encode(&[x_big.clone()]);

        let mut x_pow = vec![self.params.ringq.new_ntt_poly(); m];
        let mut x_big_pow = vec![Integer::from(1)];
        let x_big_pow_n = x_big
            .clone()
            .pow_mod(&Integer::from(self.params.n), &self.params.p)
            .unwrap();
        self.encoder.encode_assign(&x_big_pow, &mut x_pow[0]);
        for i in 1..m {
            x_big_pow[0] *= &x_big_pow_n;
            x_big_pow[0].modulo_mut(&self.params.p);
            self.encoder.encode_assign(&x_big_pow, &mut x_pow[i]);
        }

        let mut e = vec![self.params.ringq.new_ntt_poly(); self.params.l];
        for i in 0..self.params.l {
            e[i].coeffs.clone_from(&pc.h[m + 1][i].coeffs);
            self.params
                .ringq
                .mul_add_inplace(&x, &pc.h[m][i], &mut e[i]);
            for j in 0..m {
                self.params
                    .ringq
                    .mul_add_inplace(&x_pow[j], &pc.h[j][i], &mut e[i]);
            }
        }

        let mut eps = vec![self.params.ringq.new_ntt_poly(); self.params.mu + self.params.nu];
        for i in 0..self.params.mu + self.params.nu {
            eps[i].coeffs.clone_from(&pc.eta[m + 1][i].coeffs);
            self.params
                .ringq
                .mul_add_inplace(&x, &pc.eta[m][i], &mut eps[i]);
            for j in 0..m {
                self.params
                    .ringq
                    .mul_add_inplace(&x_pow[j], &pc.eta[j][i], &mut eps[i]);
            }
        }

        let mut e_intt = e.clone();
        for p in e_intt.iter_mut() {
            self.params.ringq.intt(p);
        }

        let mut e_dcd = vec![Integer::ZERO; self.params.n];
        self.encoder.decode_chunk_assign(&e_intt, &mut e_dcd);

        let mut y = Integer::ZERO;
        for i in (0..self.params.n).rev() {
            y *= x_big;
            y += &e_dcd[i];
            y.modulo_mut(&self.params.p);
        }

        return EvaluationProof {
            e: e,
            eps: eps,
            y_big: y,
        };
    }

    pub fn prove(&mut self, pc: &PolynomialCommitment) -> OpenProof {
        let m = pc.h.len() - 2;

        let s2 = ((m + 2) as f64).sqrt() * self.params.s2;
        let sig2 = ((m + 2) as f64).sqrt() * self.params.sig2;

        let mut g_raw = vec![vec![Integer::ZERO; self.params.n]; self.params.rep];
        let mut g = vec![vec![self.params.ringq.new_poly(); self.params.l]; self.params.rep];
        let mut gamma = vec![
            vec![self.params.ringq.new_poly(); self.params.mu + self.params.nu];
            self.params.rep
        ];
        let mut g_commit =
            vec![vec![self.params.ringq.new_poly(); self.params.mu]; self.params.rep];
        for i in 0..self.params.rep {
            g_raw[i].fill_with(|| self.uniform_sampler.sample_range_bigint(&self.params.p));
            self.s2_encoder
                .encode_randomized_chunk_assign(&g_raw[i], s2, &mut g[i]);
            gamma[i].iter_mut().for_each(|p| {
                self.sig2_sampler
                    .sample_poly_assign(&self.params.ringq, sig2, p);
            });
            self.committer
                .commit_assign(&g[i], &gamma[i], &mut g_commit[i]);
            g_commit[i].iter().for_each(|p| self.oracle.write_poly(p));
        }
        self.oracle.finalize();

        let mut ch = vec![vec![self.params.ringq.new_ntt_poly(); m + 1]; self.params.rep];
        ch.iter_mut()
            .flatten()
            .for_each(|p| self.oracle.read_monomial_assign(&self.params.ringq, p));

        let mut t = vec![vec![self.params.ringq.new_ntt_poly(); self.params.l]; self.params.rep];
        let mut tau = vec![
            vec![self.params.ringq.new_ntt_poly(); self.params.mu + self.params.nu];
            self.params.rep
        ];
        for i in 0..self.params.rep {
            t[i].clone_from(&g[i]);
            for j in 0..m + 1 {
                for k in 0..self.params.l {
                    self.params
                        .ringq
                        .mul_add_inplace(&ch[i][j], &pc.h[j][k], &mut t[i][k]);
                }
            }

            tau[i].clone_from(&gamma[i]);
            for j in 0..m + 1 {
                for k in 0..self.params.mu + self.params.nu {
                    self.params
                        .ringq
                        .mul_add_inplace(&ch[i][j], &pc.eta[j][k], &mut tau[i][k]);
                }
            }
        }

        return OpenProof {
            ch: ch,
            t: t,
            tau: tau,
        };
    }
}

pub struct PolynomialVerifier<'a> {
    pub params: &'a Parameters,
    pub encoder: Encoder<'a>,
    pub uniform_sampler: UniformSampler,
    pub oracle: Oracle,

    pub key: &'a CommitKey,

    pub committer: Committer<'a>,
}

impl<'a> PolynomialVerifier<'a> {
    pub fn new(params: &'a Parameters, key: &'a CommitKey) -> PolynomialVerifier<'a> {
        PolynomialVerifier {
            params: params,
            encoder: Encoder::new(params),
            uniform_sampler: UniformSampler::new(),
            oracle: Oracle::new(),

            key: key,

            committer: Committer::new(params, key),
        }
    }

    pub fn verify_evaluation(
        &mut self,
        x_big: &Integer,
        pc: &PolynomialCommitment,
        eval_pf: &EvaluationProof,
    ) -> bool {
        let mut e_intt = eval_pf.e.clone();
        for p in e_intt.iter_mut() {
            self.params.ringq.intt(p);
        }
        let mut eps_intt = eval_pf.eps.clone();
        for p in eps_intt.iter_mut() {
            self.params.ringq.intt(p);
        }

        let ev_norm2 = e_intt
            .iter()
            .chain(eps_intt.iter())
            .fold(Float::with_val(512, 0), |acc, p| {
                acc + self.params.ringq.norm(p)
            });

        if ev_norm2.log2() > 2.0 * self.params.log_bound_eval {
            return false;
        }

        let m = pc.h.len() - 2;

        let x = self.encoder.encode(&[x_big.clone()]);
        let mut x_pow = vec![self.params.ringq.new_ntt_poly(); m];
        let mut x_big_pow = vec![Integer::from(1)];
        let x_big_pow_n = x_big
            .clone()
            .pow_mod(&Integer::from(self.params.n), &self.params.p)
            .unwrap();
        self.encoder.encode_assign(&x_big_pow, &mut x_pow[0]);
        for i in 1..m {
            x_big_pow[0] *= &x_big_pow_n;
            x_big_pow[0].modulo_mut(&self.params.p);
            self.encoder.encode_assign(&x_big_pow, &mut x_pow[i]);
        }

        let mut e_dcd = vec![Integer::ZERO; self.params.n];
        self.encoder.decode_chunk_assign(&e_intt, &mut e_dcd);

        let mut y_check = e_dcd[self.params.n - 1].clone();
        for i in (0..self.params.n - 1).rev() {
            y_check *= x_big;
            y_check += &e_dcd[i];
            y_check.modulo_mut(&self.params.p);
        }

        if &eval_pf.y_big != &y_check {
            return false;
        }

        let mut commit_check = self.committer.commit(&eval_pf.e, &eval_pf.eps);
        for i in 0..self.params.mu {
            self.params
                .ringq
                .sub_inplace(&pc.h_commit[m + 1][i], &mut commit_check[i]);
            self.params
                .ringq
                .mul_sub_inplace(&x, &pc.h_commit[m][i], &mut commit_check[i]);

            for j in 0..m {
                self.params.ringq.mul_sub_inplace(
                    &x_pow[j],
                    &pc.h_commit[j][i],
                    &mut commit_check[i],
                );
            }
        }

        if commit_check.iter().any(|p| !p.is_zero()) {
            return false;
        }

        return true;
    }

    pub fn verify(&mut self, pc: &PolynomialCommitment, op: &OpenProof) -> bool {
        let m = pc.h.len() - 2;

        for i in 0..self.params.rep {
            let op_norm2 = op.t[i]
                .iter()
                .chain(op.tau[i].iter())
                .fold(Float::with_val(512, 0), |acc, p| {
                    acc + self.params.ringq.norm(p)
                });

            if op_norm2.log2() > 2.0 * self.params.log_bound_open {
                return false;
            }

            let mut g_commit_check = vec![self.params.ringq.new_ntt_poly(); self.params.mu];
            self.committer
                .commit_assign(&op.t[i], &op.tau[i], &mut g_commit_check);
            for j in 0..m + 1 {
                for k in 0..self.params.mu {
                    self.params.ringq.mul_sub_inplace(
                        &op.ch[i][j],
                        &pc.h_commit[j][k],
                        &mut g_commit_check[k],
                    );
                }
            }
            g_commit_check
                .iter()
                .for_each(|p| self.oracle.write_poly(p));
        }
        self.oracle.finalize();

        let mut mono_check = self.params.ringq.new_ntt_poly();

        for i in 0..self.params.rep {
            for j in 0..m + 1 {
                self.oracle
                    .read_monomial_assign(&self.params.ringq, &mut mono_check);
                if !op.ch[i][j].equal(&mono_check) {
                    return false;
                }
            }
        }

        return true;
    }
}
