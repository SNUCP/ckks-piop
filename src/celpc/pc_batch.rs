use rug::{Float, Integer};

use super::*;

#[derive(Clone)]
pub struct BatchPolynomialCommitment {
    pub poly_commit: PolynomialCommitment,
    pub degree: Vec<usize>,
}

#[derive(Clone)]
pub struct BatchEvaluationProof {
    pub eval_pf: EvaluationProof,
    pub y_batch: Vec<Integer>,
}

#[derive(Clone)]
pub struct BatchOpenProof {
    pub open_pf: OpenProof,
    pub degree: Vec<usize>,
}

impl<'a> PolynomialProver<'a> {
    pub fn commit_batch(&mut self, h_raw_batch: &[&[Integer]]) -> BatchPolynomialCommitment {
        let mut degree = Vec::with_capacity(h_raw_batch.len());
        for i in 0..h_raw_batch.len() {
            degree.push(h_raw_batch[i].len());
        }

        let h_raw = h_raw_batch.concat().to_vec();
        let pcs = self.commit(&h_raw);

        return BatchPolynomialCommitment {
            poly_commit: pcs,
            degree,
        };
    }

    pub fn evaluate_batch(
        &mut self,
        x0_big: &Integer,
        x1_big: &Integer,
        y_batch: &[Integer],
        pc_batch: &BatchPolynomialCommitment,
    ) -> BatchEvaluationProof {
        let m = pc_batch.poly_commit.h.len() - 2;

        let x0 = self.encoder.encode(&[x0_big.clone()]);
        let x0_big_pow_n = x0_big
            .clone()
            .pow_mod(&Integer::from(self.params.n), &self.params.p)
            .unwrap();
        let mut x_pow = Vec::with_capacity(pc_batch.degree.len());
        for i in 0..pc_batch.degree.len() {
            x_pow.push(vec![
                self.params.ringq.new_ntt_poly();
                pc_batch.degree[i] / self.params.n
            ]);
            let mut x_big_pow = vec![x1_big
                .clone()
                .pow_mod(&Integer::from(i), &self.params.p)
                .unwrap()];
            self.encoder.encode_assign(&x_big_pow, &mut x_pow[i][0]);
            for j in 1..pc_batch.degree[i] / self.params.n {
                x_big_pow[0] *= &x0_big_pow_n;
                x_big_pow[0].modulo_mut(&self.params.p);
                self.encoder.encode_assign(&x_big_pow, &mut x_pow[i][j]);
            }
        }

        let mut e = vec![self.params.ringq.new_ntt_poly(); self.params.l];
        for i in 0..self.params.l {
            e[i].coeffs
                .clone_from(&pc_batch.poly_commit.h[m + 1][i].coeffs);
            self.params
                .ringq
                .mul_add_inplace(&x0, &pc_batch.poly_commit.h[m][i], &mut e[i]);
            let mut h_idx = 0;
            for j in 0..pc_batch.degree.len() {
                for k in 0..pc_batch.degree[j] / self.params.n {
                    self.params.ringq.mul_add_inplace(
                        &x_pow[j][k],
                        &pc_batch.poly_commit.h[h_idx][i],
                        &mut e[i],
                    );
                    h_idx += 1;
                }
            }
        }

        let mut eps = vec![self.params.ringq.new_ntt_poly(); self.params.mu + self.params.nu];
        for i in 0..self.params.mu + self.params.nu {
            eps[i]
                .coeffs
                .clone_from(&pc_batch.poly_commit.eta[m + 1][i].coeffs);
            self.params
                .ringq
                .mul_add_inplace(&x0, &pc_batch.poly_commit.eta[m][i], &mut eps[i]);
            let mut eta_idx = 0;
            for j in 0..pc_batch.degree.len() {
                for k in 0..pc_batch.degree[j] / self.params.n {
                    self.params.ringq.mul_add_inplace(
                        &x_pow[j][k],
                        &pc_batch.poly_commit.eta[eta_idx][i],
                        &mut eps[i],
                    );
                    eta_idx += 1;
                }
            }
        }

        let mut y_big = Integer::ZERO;
        for i in (0..y_batch.len()).rev() {
            y_big *= x1_big;
            y_big += &y_batch[i];
            y_big.modulo_mut(&self.params.p);
        }

        return BatchEvaluationProof {
            eval_pf: EvaluationProof {
                e: e,
                eps: eps,
                y_big: y_big,
            },
            y_batch: y_batch.to_vec(),
        };
    }

    pub fn prove_batch(&mut self, pc_batch: &BatchPolynomialCommitment) -> BatchOpenProof {
        return BatchOpenProof {
            open_pf: self.prove(&pc_batch.poly_commit),
            degree: pc_batch.degree.clone(),
        };
    }
}

impl<'a> PolynomialVerifier<'a> {
    pub fn verify_evaluation_batch(
        &mut self,
        x0_big: &Integer,
        x1_big: &Integer,
        pc_batch: &BatchPolynomialCommitment,
        eval_pf_batch: &BatchEvaluationProof,
    ) -> bool {
        let mut e_intt = eval_pf_batch.eval_pf.e.clone();
        for p in e_intt.iter_mut() {
            self.params.ringq.intt(p);
        }
        let mut eps_intt = eval_pf_batch.eval_pf.eps.clone();
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

        let mut y_check = Integer::ZERO;
        for i in (0..eval_pf_batch.y_batch.len()).rev() {
            y_check *= x1_big;
            y_check += &eval_pf_batch.y_batch[i];
            y_check.modulo_mut(&self.params.p);
        }
        if y_check != eval_pf_batch.eval_pf.y_big {
            return false;
        }

        let mut e_dcd = vec![Integer::ZERO; self.params.n];
        self.encoder.decode_chunk_assign(&e_intt, &mut e_dcd);

        y_check = Integer::ZERO;
        for i in (0..self.params.n).rev() {
            y_check *= x0_big;
            y_check += &e_dcd[i];
            y_check.modulo_mut(&self.params.p);
        }

        if y_check != eval_pf_batch.eval_pf.y_big {
            return false;
        }

        let m = pc_batch.poly_commit.h.len() - 2;

        let x0 = self.encoder.encode(&[x0_big.clone()]);
        let x0_big_pow_n = x0_big
            .clone()
            .pow_mod(&Integer::from(self.params.n), &self.params.p)
            .unwrap();
        let mut x_pow = Vec::with_capacity(pc_batch.degree.len());
        for i in 0..pc_batch.degree.len() {
            x_pow.push(vec![
                self.params.ringq.new_ntt_poly();
                pc_batch.degree[i] / self.params.n
            ]);
            let mut x_big_pow = vec![x1_big
                .clone()
                .pow_mod(&Integer::from(i), &self.params.p)
                .unwrap()];
            self.encoder.encode_assign(&x_big_pow, &mut x_pow[i][0]);
            for j in 1..pc_batch.degree[i] / self.params.n {
                x_big_pow[0] *= &x0_big_pow_n;
                x_big_pow[0].modulo_mut(&self.params.p);
                self.encoder.encode_assign(&x_big_pow, &mut x_pow[i][j]);
            }
        }

        let mut commit_check = self
            .committer
            .commit(&eval_pf_batch.eval_pf.e, &eval_pf_batch.eval_pf.eps);
        for i in 0..self.params.mu {
            self.params.ringq.sub_inplace(
                &pc_batch.poly_commit.h_commit[m + 1][i],
                &mut commit_check[i],
            );
            self.params.ringq.mul_sub_inplace(
                &x0,
                &pc_batch.poly_commit.h_commit[m][i],
                &mut commit_check[i],
            );

            let mut h_idx = 0;
            for j in 0..pc_batch.degree.len() {
                for k in 0..pc_batch.degree[j] / self.params.n {
                    self.params.ringq.mul_sub_inplace(
                        &x_pow[j][k],
                        &pc_batch.poly_commit.h_commit[h_idx][i],
                        &mut commit_check[i],
                    );
                    h_idx += 1;
                }
            }
        }

        if commit_check.iter().any(|p| !p.is_zero()) {
            return false;
        }

        return true;
    }

    pub fn verify_batch(
        &mut self,
        pc_batch: &BatchPolynomialCommitment,
        open_pf: &BatchOpenProof,
    ) -> bool {
        // if pc_batch.degree.len() != open_pf.degree.len() {
        //     return false;
        // }

        // for i in 0..pc_batch.degree.len() {
        //     if pc_batch.degree[i] != open_pf.degree[i] {
        //         return false;
        //     }
        // }

        return self.verify(&pc_batch.poly_commit, &open_pf.open_pf);
    }
}
