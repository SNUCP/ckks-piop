use super::*;
use crate::csprng::Oracle;
use crate::rlwe;
use crate::{celpc, utils::signed_decompose};
use rug::ops::NegAssign;
use rug::{Assign, Complete, Integer};

fn lin_check_circuit(
    oracle: &mut Oracle,
    rlwe_evaluator: &mut rlwe::NegacyclicTransformer,
    encoder: &Encoder,
    lin_type: &[LinCheckType],
) -> PolyMultiVariatePoly {
    let params = encoder.params;

    let u = oracle.read_range_bigint(&params.rlwe.q);
    let vv = oracle.read_range_bigint(&params.rlwe.q);

    let mut v = Vec::with_capacity(params.rlwe.n);
    v.push(Integer::from(1));
    for i in 1..params.rlwe.n {
        let mut v_pow = v[i - 1].clone();
        v_pow *= &vv;
        v_pow.modulo_mut(&params.rlwe.q);
        v.push(v_pow);
    }

    let mut c = PolyMultiVariatePoly {
        coeffs: Vec::with_capacity(2 * lin_type.len()),
        max_degree: 1,
    };

    let mut u_pow = Integer::from(0);
    let mut vv = vec![Integer::ZERO; params.rlwe.n];
    let mut vv_neg = vec![Integer::ZERO; params.rlwe.n];
    for i in 0..lin_type.len() {
        let mut w_deg = vec![0; 2 * lin_type.len()];
        let mut v_deg = vec![0; 2 * lin_type.len()];
        w_deg[i] = 1;
        v_deg[i + lin_type.len()] = 1;

        for i in 0..params.rlwe.n {
            vv[i].assign(&v[i]);
            vv[i] *= &u_pow;
            vv[i].modulo_mut(&params.rlwe.q);

            vv_neg[i].assign(&vv[i]);
            vv_neg[i].neg_assign();
            vv_neg[i] += &params.rlwe.q;
        }

        u_pow *= &u;
        u_pow.modulo_mut(&params.rlwe.q);

        let mut w;
        match lin_type[i] {
            LinCheckType::NTT => {
                w = vv.clone();
                w.reverse();
                rlwe_evaluator.intt_without_normalize(&mut w);
            }
            LinCheckType::Automorphism(d) => {
                w = rlwe_evaluator
                    .automorphism(&vv, modinverse::modinverse(d, 2 * &params.rlwe.n).unwrap());
            }
        }
        let w_ecd = encoder.encode(&w);

        let vv_neg_ecd = encoder.encode(&vv_neg);

        c.coeffs.push((w_ecd, w_deg.clone()));
        c.coeffs.push((vv_neg_ecd, v_deg.clone()));
    }

    return c;
}

fn inf_norm_check_circuit(
    encoder: &Encoder,
    beta: &Integer,
    gamma: &Integer,
    input_len: usize,
    decomp_len: usize,
) -> PolyMultiVariatePoly {
    let mut c = PolyMultiVariatePoly {
        coeffs: Vec::with_capacity(input_len * (decomp_len + 1)),
        max_degree: 3,
    };

    let mut gamma_pow = Vec::with_capacity(input_len);
    gamma_pow.push(Integer::from(1));
    for i in 1..input_len {
        let mut gamma_pow_buf = gamma_pow[i - 1].clone();
        gamma_pow_buf *= gamma;
        gamma_pow_buf.modulo_mut(&encoder.params.rlwe.q);
        gamma_pow.push(gamma_pow_buf);
    }

    let mut base = Vec::with_capacity(decomp_len);
    base.push(Integer::from(1));
    base.push(Integer::from(1));
    for i in 2..decomp_len {
        base.push(Integer::from(1 << (i - 1)));
    }

    let mut beta_pow = Vec::with_capacity(decomp_len);
    beta_pow.push(beta.clone());
    for i in 1..decomp_len {
        let mut beta_pow_buf = beta_pow[i - 1].clone();
        beta_pow_buf *= beta;
        beta_pow_buf.modulo_mut(&encoder.params.rlwe.q);
        beta_pow.push(beta_pow_buf);
    }

    // We reorder the inputs as (decompose, original) for ease of implementation.
    let mut deg = vec![0; input_len * (decomp_len + 1)];
    for i in 0..input_len {
        for j in 0..decomp_len {
            deg.fill(0);
            deg[i * decomp_len + j] = 1;

            let mut lin_coeff = -beta_pow[j].clone();
            lin_coeff -= &base[j];
            lin_coeff *= &gamma_pow[i];
            lin_coeff.modulo_mut(&encoder.params.rlwe.q);
            let lin_coeff_ecd = encoder.encode(&vec![lin_coeff.clone(); encoder.params.rlwe.n]);

            c.coeffs.push((lin_coeff_ecd, deg.clone()));

            let mut cubic_coeff = beta_pow[j].clone();
            cubic_coeff *= &gamma_pow[i];
            cubic_coeff.modulo_mut(&encoder.params.rlwe.q);
            let cubic_coeff_ecd = encoder.encode(&vec![cubic_coeff.clone(); encoder.params.rlwe.n]);

            deg[i * decomp_len + j] = 3;
            c.coeffs.push((cubic_coeff_ecd, deg.clone()));
        }
    }

    for i in 0..input_len {
        deg.fill(0);
        deg[input_len * decomp_len + i] = 1;
        c.coeffs.push((
            encoder.encode(&vec![gamma_pow[i].clone(); encoder.params.rlwe.n]),
            deg.clone(),
        ));
    }

    return c;
}

pub struct Prover<'a> {
    pub params: &'a Parameters,

    pub encoder: Encoder<'a>,
    pub celpc_prover: celpc::PolynomialProver<'a>,

    pub oracle: Oracle,

    pub ringq: BigRing,
    pub neg_transformer: rlwe::NegacyclicTransformer,
}

impl<'a> Prover<'a> {
    pub fn new(params: &'a Parameters, ck: &'a celpc::CommitKey) -> Self {
        let encoder = Encoder::new(params);

        Prover {
            params: params,
            encoder: encoder,

            celpc_prover: celpc::PolynomialProver::new(&params.pcs, ck),
            oracle: Oracle::new(),

            ringq: BigRing::new(params.embedding_n, &params.rlwe.q),
            neg_transformer: rlwe::NegacyclicTransformer::new(params.rlwe.n, &params.rlwe.q),
        }
    }

    pub fn sum_check_oracle(
        &mut self,
        ai_ntt: &[&BigPoly],
        c_ntt: &PolyMultiVariatePoly,
    ) -> (SumCheckPoly, SumCheckOracle) {
        // Move 1
        // g has degree d(2N - 1) + N - 1
        let mut g = self.ringq.new_poly();
        let g_degree = c_ntt.max_degree * (2 * self.params.rlwe.n - 1) + self.params.rlwe.n - 1;
        for i in 0..self.params.rlwe.n {
            g.coeffs[i] = self
                .encoder
                .uniform_sampler
                .sample_range_bigint(&self.params.rlwe.q);
        }
        let mu = g.coeffs[0].clone();
        for i in 0..g_degree - self.params.rlwe.n {
            let c = self
                .encoder
                .uniform_sampler
                .sample_range_bigint(&self.params.rlwe.q);

            // Add c * X^i * (X^N - 1)
            g.coeffs[i] -= &c;
            if g.coeffs[i].is_negative() {
                g.coeffs[i] += &self.params.rlwe.q;
            }

            g.coeffs[i + self.params.rlwe.n] += &c;
            if g.coeffs[i + self.params.rlwe.n] >= self.params.rlwe.q {
                g.coeffs[i + self.params.rlwe.n] -= &self.params.rlwe.q;
            }
        }

        let g_oracle = self.celpc_prover.gen_poly_oracle(&g.coeffs);

        // Move 2
        self.oracle.write_polynomial_oracle(&g_oracle);
        self.oracle.write_bigint(&mu);
        self.oracle.finalize();

        let beta = self.oracle.read_range_bigint(&self.params.rlwe.q);

        // Move 3
        let mut check_eval = self.ringq.evaluate_poly_multivariate_poly(c_ntt, ai_ntt);
        self.ringq.intt_inplace(&mut check_eval);
        self.ringq.mul_const_inplace(&beta, &mut check_eval);
        self.ringq.add_inplace(&g, &mut check_eval);

        // quo has degree d * (2N - 1) - 1 < 2dN
        // rem has degree N - 2 < N
        let (quo, mut rem) = self.ringq.quo_rem_zero(&check_eval, self.params.rlwe.n);
        rem.coeffs[0] = Integer::ZERO;

        let quo_rem_oracle = self.celpc_prover.gen_batch_poly_oracle(&[
            &quo.coeffs[..2 * c_ntt.max_degree * self.params.rlwe.n],
            &rem.coeffs[..self.params.rlwe.n],
        ]);

        let sum_check_poly = SumCheckPoly {
            g: g,
            quo: quo,
            rem: rem,
        };
        let sum_check_oracle = SumCheckOracle {
            g_oracle: g_oracle,
            quo_rem_oracle: quo_rem_oracle,

            mu: mu,
        };

        return (sum_check_poly, sum_check_oracle);
    }

    pub fn sum_check_eval(
        &mut self,
        alpha: &Integer,
        alpha_combine: &Integer,
        sum_check_poly: &SumCheckPoly,
        sum_check_oracle: &SumCheckOracle,
    ) -> SumCheckEvalProof {
        let quo_eval = self.ringq.evaluate(&sum_check_poly.quo, alpha);
        let rem_eval = self.ringq.evaluate(&sum_check_poly.rem, alpha);

        let g_eval_pf = self
            .celpc_prover
            .evaluate(alpha, &sum_check_oracle.g_oracle.commitment);
        let quo_rem_eval_pf = self.celpc_prover.evaluate_batch(
            alpha,
            alpha_combine,
            &[quo_eval, rem_eval],
            &sum_check_oracle.quo_rem_oracle.commitment,
        );

        return SumCheckEvalProof {
            g_eval_pf: g_eval_pf,
            quo_rem_eval_pf,
        };
    }

    pub fn arith_check_oracle(
        &mut self,
        ai_ntt: &[&BigPoly],
        c_ntt: &PolyMultiVariatePoly,
    ) -> (ArithCheckPoly, ArithCheckOracle) {
        let mut check = self.ringq.evaluate_poly_multivariate_poly(&c_ntt, ai_ntt);
        self.ringq.intt_inplace(&mut check);
        let (quo, _) = self.ringq.quo_rem_zero(&check, self.params.rlwe.n);
        let quo_oracle = self.celpc_prover.gen_poly_oracle(&quo.coeffs);

        return (
            ArithCheckPoly { quo: quo },
            ArithCheckOracle {
                quo_oracle: quo_oracle,
            },
        );
    }

    pub fn arith_check_eval(
        &mut self,
        alpha: &Integer,
        arith_check_oracle: &ArithCheckOracle,
    ) -> ArithCheckEvalProof {
        let quo_eval_pf = self
            .celpc_prover
            .evaluate(&alpha, &arith_check_oracle.quo_oracle.commitment);

        return ArithCheckEvalProof {
            quo_eval_pf: quo_eval_pf,
        };
    }

    pub fn lin_check_circuit(&mut self, lin_type: &[LinCheckType]) -> PolyMultiVariatePoly {
        let mut c = lin_check_circuit(
            &mut self.oracle,
            &mut self.neg_transformer,
            &self.encoder,
            lin_type,
        );

        for i in 0..c.coeffs.len() {
            self.ringq.ntt_inplace(&mut c.coeffs[i].0);
        }

        return c;
    }

    pub fn inf_norm_check(
        &mut self,
        ai_dcd: &[&[Integer]],
        ai: &[&BigPoly],
        log_bound: usize,
    ) -> InfNormSetup {
        let mut decomposed = Vec::with_capacity(ai.len() * (log_bound + 2));

        for i in 0..ai.len() {
            let mut decomposed_buf = vec![vec![Integer::ZERO; self.params.rlwe.n]; log_bound + 1];
            for j in 0..self.params.rlwe.n {
                let coeffs_decomposed = signed_decompose(&ai_dcd[i][j], log_bound);
                for k in 0..log_bound + 1 {
                    decomposed_buf[k][j].assign(&coeffs_decomposed[k]);
                }
            }
            for j in 0..log_bound + 1 {
                decomposed.push(self.encoder.encode_randomize(&decomposed_buf[j]));
            }
        }

        for i in 0..ai.len() {
            decomposed.push(ai[i].clone());
        }

        let mut decomposed_ref = Vec::with_capacity(decomposed.len());
        for i in 0..decomposed.len() {
            decomposed_ref.push(&decomposed[i].coeffs[..]);
        }

        let decomposed_oracle = self.celpc_prover.gen_batch_poly_oracle(&decomposed_ref);

        self.oracle
            .write_batch_polynomial_oracle(&decomposed_oracle);
        self.oracle.finalize();

        let beta = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let gamma = self.oracle.read_range_bigint(&self.params.rlwe.q);

        let mut inf_norm_circuit =
            inf_norm_check_circuit(&self.encoder, &beta, &gamma, ai.len(), log_bound + 1);

        for i in 0..inf_norm_circuit.coeffs.len() {
            self.ringq.ntt_inplace(&mut inf_norm_circuit.coeffs[i].0);
        }

        let mut decomposed_ntt = Vec::with_capacity(decomposed.len());
        for i in 0..decomposed.len() {
            decomposed_ntt.push(self.ringq.ntt(&decomposed[i]));
        }

        return InfNormSetup {
            decomposed: decomposed,
            decomposed_ntt: decomposed_ntt,
            decomposed_oracles: decomposed_oracle,
            circuit: inf_norm_circuit,
        };
    }

    pub fn two_norm_check(&mut self, ai_dcd: &[Integer], log_bound: usize) -> TwoNormSetup {
        let mut base_neg = vec![Integer::ZERO; self.params.rlwe.n];
        base_neg[0].assign(-1);
        for i in 0..2 * log_bound {
            base_neg[i + 1].assign(-(1 << i));
        }
        let mut c_neg = vec![Integer::ZERO; self.params.rlwe.n];
        for i in 0..2 * log_bound + 1 {
            c_neg[i].assign(-1);
        }

        let mut base_neg_ecd = self.encoder.encode(&base_neg);
        let mut c_neg_ecd = self.encoder.encode(&c_neg);
        let mut one_ecd = self
            .encoder
            .encode(&vec![Integer::from(1); self.params.rlwe.n]);
        self.ringq.ntt_inplace(&mut base_neg_ecd);
        self.ringq.ntt_inplace(&mut c_neg_ecd);
        self.ringq.ntt_inplace(&mut one_ecd);

        let arith_circuit = PolyMultiVariatePoly {
            coeffs: vec![(one_ecd.clone(), vec![2]), (c_neg_ecd, vec![1])],
            max_degree: 2,
        };
        let sum_circuit = PolyMultiVariatePoly {
            coeffs: vec![(one_ecd.clone(), vec![1, 0]), (base_neg_ecd, vec![0, 1])],
            max_degree: 1,
        };

        let mut a_dcd_norm = Integer::ZERO;
        let mut sum = Integer::ZERO;
        for i in 0..ai_dcd.len() {
            sum.assign(&ai_dcd[i]);
            sum *= &ai_dcd[i];
            a_dcd_norm += &sum;
            a_dcd_norm.modulo_mut(&self.params.rlwe.q);
        }

        let mut u = signed_decompose(&a_dcd_norm, 2 * log_bound);
        for _ in u.len()..self.params.rlwe.n {
            u.push(Integer::ZERO);
        }
        let u_ecd = self.encoder.encode_randomize(&u);
        let u_ecd_ntt = self.ringq.ntt(&u_ecd);
        let u_oracle = self.celpc_prover.gen_poly_oracle(&u_ecd.coeffs);

        return TwoNormSetup {
            u: u_ecd,
            u_ntt: u_ecd_ntt,
            u_oracle: u_oracle,

            arith_circuit: arith_circuit,
            sum_circuit: sum_circuit,
        };
    }

    pub fn prove_ckks(
        &mut self,
        cts: &[rlwe::Ciphertext],
        sk: &rlwe::SecretKey,
        pk: &rlwe::PublicKey,
        rlk: &rlwe::RelinKey,
        atk: &rlwe::AutomorphismKey,
        cjk: &rlwe::AutomorphismKey,
    ) -> CKKSProof {
        let level = self.params.rlwe.gadget.len();
        let ct_count = cts.len();

        let m_coeffs = (0..ct_count)
            .map(|i| self.encoder.encode_randomize(&cts[i].m_coeffs))
            .collect::<Vec<_>>();
        let m_ntt = (0..ct_count)
            .map(|i| self.encoder.encode_randomize(&cts[i].m_ntt))
            .collect::<Vec<_>>();
        let ect_coeffs = (0..ct_count)
            .map(|i| self.encoder.encode_randomize(&cts[i].e_coeffs))
            .collect::<Vec<_>>();
        let ect_ntt = (0..ct_count)
            .map(|i| self.encoder.encode_randomize(&cts[i].e_ntt))
            .collect::<Vec<_>>();
        let s_coeffs = self.encoder.encode_randomize(&sk.coeffs);
        let s_ntt = self.encoder.encode_randomize(&sk.ntt);
        let satk_ntt = self.encoder.encode_randomize(&atk.satk_ntt);
        let scjk_ntt = self.encoder.encode_randomize(&cjk.satk_ntt);
        let epk_coeffs = self.encoder.encode_randomize(&pk.epk_coeffs);
        let epk_ntt = self.encoder.encode_randomize(&pk.epk_ntt);
        let erlk_coeffs = (0..level)
            .map(|i| self.encoder.encode_randomize(&rlk.erlk_coeffs[i]))
            .collect::<Vec<_>>();
        let erlk_ntt = (0..level)
            .map(|i| self.encoder.encode_randomize(&rlk.erlk_ntt[i]))
            .collect::<Vec<_>>();
        let eatk_coeffs = (0..level)
            .map(|i| self.encoder.encode_randomize(&atk.eatk_coeffs[i]))
            .collect::<Vec<_>>();
        let eatk_ntt = (0..level)
            .map(|i| self.encoder.encode_randomize(&atk.eatk_ntt[i]))
            .collect::<Vec<_>>();
        let ecjk_coeffs = (0..level)
            .map(|i| self.encoder.encode_randomize(&cjk.eatk_coeffs[i]))
            .collect::<Vec<_>>();
        let ecjk_ntt = (0..level)
            .map(|i| self.encoder.encode_randomize(&cjk.eatk_ntt[i]))
            .collect::<Vec<_>>();

        let m_coeffs_ntt = m_coeffs
            .iter()
            .map(|m| self.ringq.ntt(m))
            .collect::<Vec<_>>();
        let m_ntt_ntt = m_ntt.iter().map(|m| self.ringq.ntt(m)).collect::<Vec<_>>();
        let ect_coeffs_ntt = ect_coeffs
            .iter()
            .map(|e| self.ringq.ntt(e))
            .collect::<Vec<_>>();
        let ect_ntt_ntt = ect_ntt
            .iter()
            .map(|e| self.ringq.ntt(e))
            .collect::<Vec<_>>();
        let s_coeffs_ntt = self.ringq.ntt(&s_coeffs);
        let s_ntt_ntt = self.ringq.ntt(&s_ntt);
        let satk_ntt_ntt = self.ringq.ntt(&satk_ntt);
        let scjk_ntt_ntt = self.ringq.ntt(&scjk_ntt);
        let epk_coeffs_ntt = self.ringq.ntt(&epk_coeffs);
        let epk_ntt_ntt = self.ringq.ntt(&epk_ntt);
        let erlk_coeffs_ntt = erlk_coeffs
            .iter()
            .map(|e| self.ringq.ntt(e))
            .collect::<Vec<_>>();
        let erlk_ntt_ntt = erlk_ntt
            .iter()
            .map(|e| self.ringq.ntt(e))
            .collect::<Vec<_>>();
        let eatk_coeffs_ntt = eatk_coeffs
            .iter()
            .map(|e| self.ringq.ntt(e))
            .collect::<Vec<_>>();
        let eatk_ntt_ntt = eatk_ntt
            .iter()
            .map(|e| self.ringq.ntt(e))
            .collect::<Vec<_>>();
        let ecjk_coeffs_ntt = ecjk_coeffs
            .iter()
            .map(|e| self.ringq.ntt(e))
            .collect::<Vec<_>>();
        let ecjk_ntt_ntt = ecjk_ntt
            .iter()
            .map(|e| self.ringq.ntt(e))
            .collect::<Vec<_>>();

        // CKKS polynomial length equals
        // 6 + level * 6 + 4 * ct_count
        let ckks_oracle_len = 6 + level * 6 + 4 * ct_count;
        let mut ckks_coeffs_ref = Vec::with_capacity(ckks_oracle_len);
        ckks_coeffs_ref.push(&s_coeffs.coeffs[..]);
        ckks_coeffs_ref.push(&s_ntt.coeffs[..]);
        ckks_coeffs_ref.push(&satk_ntt.coeffs[..]);
        ckks_coeffs_ref.push(&scjk_ntt.coeffs[..]);
        ckks_coeffs_ref.push(&epk_coeffs.coeffs[..]);
        ckks_coeffs_ref.push(&epk_ntt.coeffs[..]);
        for i in 0..level {
            ckks_coeffs_ref.push(&erlk_coeffs[i].coeffs[..]);
            ckks_coeffs_ref.push(&erlk_ntt[i].coeffs[..]);
            ckks_coeffs_ref.push(&eatk_coeffs[i].coeffs[..]);
            ckks_coeffs_ref.push(&eatk_ntt[i].coeffs[..]);
            ckks_coeffs_ref.push(&ecjk_coeffs[i].coeffs[..]);
            ckks_coeffs_ref.push(&ecjk_ntt[i].coeffs[..]);
        }
        for i in 0..ct_count {
            ckks_coeffs_ref.push(&m_coeffs[i].coeffs[..]);
            ckks_coeffs_ref.push(&m_ntt[i].coeffs[..]);
            ckks_coeffs_ref.push(&ect_coeffs[i].coeffs[..]);
            ckks_coeffs_ref.push(&ect_ntt[i].coeffs[..]);
        }

        let ckks_oracle = self.celpc_prover.gen_batch_poly_oracle(&ckks_coeffs_ref);

        self.oracle.write_batch_polynomial_oracle(&ckks_oracle);
        self.oracle.finalize();

        let gamma = self.oracle.read_range_bigint(&self.params.rlwe.q);

        // sk inf norm check
        let sk_inf_norm_setup = self.inf_norm_check(&[&sk.coeffs], &[&s_coeffs], 0);
        let mut sk_inf_norm_decomposed_ntt =
            Vec::with_capacity(sk_inf_norm_setup.decomposed_ntt.len());
        for i in 0..sk_inf_norm_setup.decomposed_ntt.len() {
            sk_inf_norm_decomposed_ntt.push(&sk_inf_norm_setup.decomposed_ntt[i]);
        }
        let (_, sk_inf_norm_oracle) =
            self.arith_check_oracle(&sk_inf_norm_decomposed_ntt, &sk_inf_norm_setup.circuit);

        // sk two norm check
        let sk_two_norm_setup = self.two_norm_check(
            &sk.coeffs,
            self.params.rlwe.s_hamming_weight.ilog2() as usize,
        );
        let (_, sk_two_norm_arith_oracle) = self.arith_check_oracle(
            &[&sk_two_norm_setup.u_ntt],
            &sk_two_norm_setup.arith_circuit,
        );
        let (sk_two_norm_sumcheck_poly, sk_two_norm_sumcheck_oracle) = self.sum_check_oracle(
            &[&s_coeffs_ntt, &sk_two_norm_setup.u_ntt],
            &sk_two_norm_setup.sum_circuit,
        );

        // message inf norm check
        let mut m_inf_norm_check_input_dcd = Vec::with_capacity(ct_count);
        let mut m_inf_norm_check_input = Vec::with_capacity(ct_count);
        for i in 0..ct_count {
            m_inf_norm_check_input_dcd.push(&cts[i].m_coeffs[..]);
            m_inf_norm_check_input.push(&m_coeffs[i]);
        }
        let m_inf_norm_setup = self.inf_norm_check(
            &m_inf_norm_check_input_dcd,
            &m_inf_norm_check_input,
            cts[0].m_log_bound,
        );
        let mut m_inf_norm_decomposed_ntt =
            Vec::with_capacity(m_inf_norm_setup.decomposed_ntt.len());
        for i in 0..m_inf_norm_setup.decomposed_ntt.len() {
            m_inf_norm_decomposed_ntt.push(&m_inf_norm_setup.decomposed_ntt[i]);
        }
        let (_, m_inf_norm_oracle) =
            self.arith_check_oracle(&m_inf_norm_decomposed_ntt, &m_inf_norm_setup.circuit);

        // err inf norm check
        // epr, erlk, eatk, ecjk
        let err_inf_norm_check_len = 1 + 3 * level;
        let mut err_inf_norm_check_input_dcd = Vec::with_capacity(err_inf_norm_check_len);
        let mut err_inf_norm_check_input = Vec::with_capacity(err_inf_norm_check_len);
        err_inf_norm_check_input_dcd.push(&pk.epk_coeffs[..]);
        err_inf_norm_check_input.push(&epk_coeffs);
        for i in 0..level {
            err_inf_norm_check_input_dcd.push(&rlk.erlk_coeffs[i]);
            err_inf_norm_check_input.push(&erlk_coeffs[i]);
            err_inf_norm_check_input_dcd.push(&atk.eatk_coeffs[i]);
            err_inf_norm_check_input.push(&eatk_coeffs[i]);
            err_inf_norm_check_input_dcd.push(&cjk.eatk_coeffs[i]);
            err_inf_norm_check_input.push(&ecjk_coeffs[i]);
        }
        let e_inf_norm_setup = self.inf_norm_check(
            &err_inf_norm_check_input_dcd,
            &err_inf_norm_check_input,
            self.params.rlwe.log_e_bound,
        );
        let mut e_inf_norm_decomposed_ntt =
            Vec::with_capacity(e_inf_norm_setup.decomposed_ntt.len());
        for i in 0..e_inf_norm_setup.decomposed_ntt.len() {
            e_inf_norm_decomposed_ntt.push(&e_inf_norm_setup.decomposed_ntt[i]);
        }
        let (_, e_inf_norm_oracle) =
            self.arith_check_oracle(&e_inf_norm_decomposed_ntt, &e_inf_norm_setup.circuit);

        // Automoprhism Check:
        let aut_circuit = self.lin_check_circuit(&[
            LinCheckType::Automorphism(atk.d),
            LinCheckType::Automorphism(cjk.d),
        ]);
        let (aut_poly, aut_oracle) = self.sum_check_oracle(
            &[&s_ntt_ntt, &s_ntt_ntt, &satk_ntt_ntt, &scjk_ntt_ntt],
            &aut_circuit,
        );

        // NTT Check:
        // s, m, ect, epk, erlk, eatk, ecjk
        let ntt_check_len = 2 + 2 * ct_count + 3 * level;
        let mut ntt_check_inputs_ntt = Vec::with_capacity(ntt_check_len * 2);
        ntt_check_inputs_ntt.push(&s_coeffs_ntt);
        ntt_check_inputs_ntt.push(&epk_coeffs_ntt);
        for i in 0..ct_count {
            ntt_check_inputs_ntt.push(&m_coeffs_ntt[i]);
            ntt_check_inputs_ntt.push(&ect_coeffs_ntt[i]);
        }
        for i in 0..level {
            ntt_check_inputs_ntt.push(&erlk_coeffs_ntt[i]);
            ntt_check_inputs_ntt.push(&eatk_coeffs_ntt[i]);
            ntt_check_inputs_ntt.push(&ecjk_coeffs_ntt[i]);
        }
        ntt_check_inputs_ntt.push(&s_ntt_ntt);
        ntt_check_inputs_ntt.push(&epk_ntt_ntt);
        for i in 0..ct_count {
            ntt_check_inputs_ntt.push(&m_ntt_ntt[i]);
            ntt_check_inputs_ntt.push(&ect_ntt_ntt[i]);
        }
        for i in 0..level {
            ntt_check_inputs_ntt.push(&erlk_ntt_ntt[i]);
            ntt_check_inputs_ntt.push(&eatk_ntt_ntt[i]);
            ntt_check_inputs_ntt.push(&ecjk_ntt_ntt[i]);
        }

        let ntt_circuit = self.lin_check_circuit(&vec![LinCheckType::NTT; ntt_check_len]);
        let (ntt_poly, ntt_oracle) = self.sum_check_oracle(&ntt_check_inputs_ntt, &ntt_circuit);

        // pk check
        let neg_one = self.params.rlwe.q.clone() - Integer::ONE;
        let mut pk0_ntt_ecd = self.encoder.encode(&pk.b_ntt);
        let mut pk1_ntt_ecd = self.encoder.encode(&pk.a_ntt);
        let mut neg_one_ecd = self
            .encoder
            .encode(&vec![neg_one.clone(); self.params.rlwe.n]);
        self.ringq.ntt_inplace(&mut pk0_ntt_ecd);
        self.ringq.ntt_inplace(&mut pk1_ntt_ecd);
        self.ringq.ntt_inplace(&mut neg_one_ecd);
        let pk_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (pk0_ntt_ecd, vec![0, 0]),
                (pk1_ntt_ecd, vec![1, 0]),
                (neg_one_ecd, vec![0, 1]),
            ],
            max_degree: 1,
        };

        let (_, pk_oracle) = self.arith_check_oracle(&[&s_ntt_ntt, &epk_ntt_ntt], &pk_circuit);

        // ksk check
        let mut gamma_pow_neg = vec![Integer::ZERO; usize::max(level, ct_count)];
        gamma_pow_neg[0] = neg_one.clone();
        for i in 1..gamma_pow_neg.len() {
            gamma_pow_neg[i] = gamma_pow_neg[i - 1].clone();
            gamma_pow_neg[i] *= &gamma;
            gamma_pow_neg[i].modulo_mut(&self.params.rlwe.q);
        }

        let mut gamma_pow_neg_ecd = Vec::with_capacity(gamma_pow_neg.len());
        for i in 0..gamma_pow_neg.len() {
            gamma_pow_neg_ecd.push(
                self.encoder
                    .encode(&vec![gamma_pow_neg[i].clone(); self.params.rlwe.n]),
            );
            self.ringq.ntt_inplace(&mut gamma_pow_neg_ecd[i]);
        }

        let mut rlk0 = vec![Integer::from(0); self.params.rlwe.n];
        let mut rlk1 = vec![Integer::from(0); self.params.rlwe.n];
        let mut atk0 = vec![Integer::from(0); self.params.rlwe.n];
        let mut atk1 = vec![Integer::from(0); self.params.rlwe.n];
        let mut cjk0 = vec![Integer::from(0); self.params.rlwe.n];
        let mut cjk1 = vec![Integer::from(0); self.params.rlwe.n];
        let mut gad = vec![Integer::from(0); self.params.rlwe.n];
        for i in (0..level).rev() {
            for j in 0..self.params.rlwe.n {
                rlk0[j] *= &gamma;
                rlk0[j] += &rlk.b_ntt[i][j];
                rlk0[j].modulo_mut(&self.params.rlwe.q);

                rlk1[j] *= &gamma;
                rlk1[j] += &rlk.a_ntt[i][j];
                rlk1[j].modulo_mut(&self.params.rlwe.q);

                atk0[j] *= &gamma;
                atk0[j] += &atk.b_ntt[i][j];
                atk0[j].modulo_mut(&self.params.rlwe.q);

                atk1[j] *= &gamma;
                atk1[j] += &atk.a_ntt[i][j];
                atk1[j].modulo_mut(&self.params.rlwe.q);

                cjk0[j] *= &gamma;
                cjk0[j] += &cjk.b_ntt[i][j];
                cjk0[j].modulo_mut(&self.params.rlwe.q);

                cjk1[j] *= &gamma;
                cjk1[j] += &cjk.a_ntt[i][j];
                cjk1[j].modulo_mut(&self.params.rlwe.q);

                gad[j] *= &gamma;
                gad[j] -= &self.params.rlwe.gadget[i];
                gad[j].modulo_mut(&self.params.rlwe.q);
            }
        }
        let mut ct0 = vec![Integer::from(0); self.params.rlwe.n];
        let mut ct1 = vec![Integer::from(0); self.params.rlwe.n];
        for i in (0..ct_count).rev() {
            for j in 0..self.params.rlwe.n {
                ct0[j] *= &gamma;
                ct0[j] += &cts[i].b_ntt[j];
                ct0[j].modulo_mut(&self.params.rlwe.q);

                ct1[j] *= &gamma;
                ct1[j] += &cts[i].a_ntt[j];
                ct1[j].modulo_mut(&self.params.rlwe.q);
            }
        }

        let mut rlk0_ecd = self.encoder.encode(&rlk0);
        let mut rlk1_ecd = self.encoder.encode(&rlk1);
        let mut atk0_ecd = self.encoder.encode(&atk0);
        let mut atk1_ecd = self.encoder.encode(&atk1);
        let mut cjk0_ecd = self.encoder.encode(&cjk0);
        let mut cjk1_ecd = self.encoder.encode(&cjk1);
        let mut gad_ecd = self.encoder.encode(&gad);
        let mut ct0_ecd = self.encoder.encode(&ct0);
        let mut ct1_ecd = self.encoder.encode(&ct1);

        self.ringq.ntt_inplace(&mut rlk0_ecd);
        self.ringq.ntt_inplace(&mut rlk1_ecd);
        self.ringq.ntt_inplace(&mut atk0_ecd);
        self.ringq.ntt_inplace(&mut atk1_ecd);
        self.ringq.ntt_inplace(&mut cjk0_ecd);
        self.ringq.ntt_inplace(&mut cjk1_ecd);
        self.ringq.ntt_inplace(&mut gad_ecd);
        self.ringq.ntt_inplace(&mut ct0_ecd);
        self.ringq.ntt_inplace(&mut ct1_ecd);

        let mut rlk_circuit = PolyMultiVariatePoly {
            coeffs: Vec::with_capacity(level + 1),
            max_degree: 2,
        };
        let mut deg = vec![0; level + 1];
        rlk_circuit.coeffs.push((rlk0_ecd, deg.clone()));
        deg.fill(0);
        deg[0] = 1;
        rlk_circuit.coeffs.push((rlk1_ecd, deg.clone()));
        deg.fill(0);
        deg[0] = 2;
        rlk_circuit.coeffs.push((gad_ecd.clone(), deg.clone()));
        for j in 0..level {
            deg.fill(0);
            deg[j + 1] = 1;
            rlk_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[j].clone(), deg.clone()));
        }

        let mut atk_circuit = PolyMultiVariatePoly {
            coeffs: Vec::with_capacity(level + 2),
            max_degree: 1,
        };
        let mut cjk_circuit = PolyMultiVariatePoly {
            coeffs: Vec::with_capacity(level + 2),
            max_degree: 1,
        };
        deg = vec![0; level + 2];
        atk_circuit.coeffs.push((atk0_ecd, deg.clone()));
        cjk_circuit.coeffs.push((cjk0_ecd, deg.clone()));
        deg.fill(0);
        deg[0] = 1;
        atk_circuit.coeffs.push((atk1_ecd, deg.clone()));
        cjk_circuit.coeffs.push((cjk1_ecd, deg.clone()));
        deg.fill(0);
        deg[1] = 1;
        atk_circuit.coeffs.push((gad_ecd.clone(), deg.clone()));
        cjk_circuit.coeffs.push((gad_ecd.clone(), deg.clone()));
        for j in 0..level {
            deg.fill(0);
            deg[j + 2] = 1;
            atk_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[j].clone(), deg.clone()));
            cjk_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[j].clone(), deg.clone()));
        }

        let mut ct_circuit = PolyMultiVariatePoly {
            coeffs: Vec::with_capacity(ct_count * 2 + 1),
            max_degree: 1,
        };
        deg = vec![0; ct_count * 2 + 1];
        ct_circuit.coeffs.push((ct0_ecd, deg.clone()));
        deg[0] = 1;
        ct_circuit.coeffs.push((ct1_ecd, deg.clone()));
        for i in 0..ct_count {
            deg.fill(0);
            deg[i * 2 + 1] = 1;
            ct_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[i].clone(), deg.clone()));
            deg.fill(0);
            deg[i * 2 + 2] = 1;
            ct_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[i].clone(), deg.clone()));
        }

        let mut rlk_check_inputs_ntt = Vec::with_capacity(level + 1);
        rlk_check_inputs_ntt.push(&s_ntt_ntt);
        for i in 0..level {
            rlk_check_inputs_ntt.push(&erlk_ntt_ntt[i]);
        }
        let (_, rlk_oracle) = self.arith_check_oracle(&rlk_check_inputs_ntt, &rlk_circuit);

        let mut atk_check_inputs_ntt = Vec::with_capacity(level + 2);
        atk_check_inputs_ntt.push(&s_ntt_ntt);
        atk_check_inputs_ntt.push(&satk_ntt_ntt);
        for i in 0..level {
            atk_check_inputs_ntt.push(&eatk_ntt_ntt[i]);
        }
        let (_, atk_oracle) = self.arith_check_oracle(&atk_check_inputs_ntt, &atk_circuit);

        let mut cjk_check_inputs_ntt = Vec::with_capacity(level + 2);
        cjk_check_inputs_ntt.push(&s_ntt_ntt);
        cjk_check_inputs_ntt.push(&scjk_ntt_ntt);
        for i in 0..level {
            cjk_check_inputs_ntt.push(&ecjk_ntt_ntt[i]);
        }
        let (_, cjk_oracle) = self.arith_check_oracle(&cjk_check_inputs_ntt, &cjk_circuit);

        let mut ct_check_inputs_ntt = Vec::with_capacity(ct_count * 2 + 1);
        ct_check_inputs_ntt.push(&s_ntt_ntt);
        for i in 0..ct_count {
            ct_check_inputs_ntt.push(&m_ntt_ntt[i]);
            ct_check_inputs_ntt.push(&ect_ntt_ntt[i]);
        }
        let (_, ct_oracle) = self.arith_check_oracle(&ct_check_inputs_ntt, &ct_circuit);

        self.oracle.write_arithcheck_oracle(&sk_inf_norm_oracle);
        self.oracle
            .write_arithcheck_oracle(&sk_two_norm_arith_oracle);
        self.oracle
            .write_sumcheck_oracle(&sk_two_norm_sumcheck_oracle);
        self.oracle.write_arithcheck_oracle(&m_inf_norm_oracle);
        self.oracle.write_arithcheck_oracle(&e_inf_norm_oracle);
        self.oracle.write_sumcheck_oracle(&aut_oracle);
        self.oracle.write_sumcheck_oracle(&ntt_oracle);
        self.oracle.write_arithcheck_oracle(&pk_oracle);
        self.oracle.write_arithcheck_oracle(&rlk_oracle);
        self.oracle.write_arithcheck_oracle(&atk_oracle);
        self.oracle.write_arithcheck_oracle(&cjk_oracle);
        self.oracle.write_arithcheck_oracle(&ct_oracle);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        let mut ckks_eval = Vec::with_capacity(ckks_oracle_len);
        ckks_eval.push(self.ringq.evaluate(&s_coeffs, &alpha));
        ckks_eval.push(self.ringq.evaluate(&s_ntt, &alpha));
        ckks_eval.push(self.ringq.evaluate(&satk_ntt, &alpha));
        ckks_eval.push(self.ringq.evaluate(&scjk_ntt, &alpha));
        ckks_eval.push(self.ringq.evaluate(&epk_coeffs, &alpha));
        ckks_eval.push(self.ringq.evaluate(&epk_ntt, &alpha));
        for i in 0..level {
            ckks_eval.push(self.ringq.evaluate(&erlk_coeffs[i], &alpha));
            ckks_eval.push(self.ringq.evaluate(&erlk_ntt[i], &alpha));
            ckks_eval.push(self.ringq.evaluate(&eatk_coeffs[i], &alpha));
            ckks_eval.push(self.ringq.evaluate(&eatk_ntt[i], &alpha));
            ckks_eval.push(self.ringq.evaluate(&ecjk_coeffs[i], &alpha));
            ckks_eval.push(self.ringq.evaluate(&ecjk_ntt[i], &alpha));
        }
        for i in 0..ct_count {
            ckks_eval.push(self.ringq.evaluate(&m_coeffs[i], &alpha));
            ckks_eval.push(self.ringq.evaluate(&m_ntt[i], &alpha));
            ckks_eval.push(self.ringq.evaluate(&ect_coeffs[i], &alpha));
            ckks_eval.push(self.ringq.evaluate(&ect_ntt[i], &alpha));
        }

        let ckks_eval_pf = self.celpc_prover.evaluate_batch(
            &alpha,
            &alpha_combine,
            &ckks_eval,
            &ckks_oracle.commitment,
        );

        let mut sk_inf_norm_decomposed_eval =
            Vec::with_capacity(sk_inf_norm_setup.decomposed.len());
        for i in 0..sk_inf_norm_setup.decomposed.len() {
            sk_inf_norm_decomposed_eval.push(
                self.ringq
                    .evaluate(&sk_inf_norm_setup.decomposed[i], &alpha),
            );
        }
        let sk_inf_norm_decomposed_eval_pf = self.celpc_prover.evaluate_batch(
            &alpha,
            &alpha_combine,
            &sk_inf_norm_decomposed_eval,
            &sk_inf_norm_setup.decomposed_oracles.commitment,
        );
        let sk_inf_norm_eval_pf = self.arith_check_eval(&alpha, &sk_inf_norm_oracle);

        let sk_two_norm_eval_pf = self
            .celpc_prover
            .evaluate(&alpha, &sk_two_norm_setup.u_oracle.commitment);
        let sk_two_norm_arith_eval_pf = self.arith_check_eval(&alpha, &sk_two_norm_arith_oracle);
        let sk_two_norm_sumcheck_eval_pf = self.sum_check_eval(
            &alpha,
            &alpha_combine,
            &sk_two_norm_sumcheck_poly,
            &sk_two_norm_sumcheck_oracle,
        );

        let mut m_inf_norm_decomposed_eval = Vec::with_capacity(m_inf_norm_setup.decomposed.len());
        for i in 0..m_inf_norm_setup.decomposed.len() {
            m_inf_norm_decomposed_eval
                .push(self.ringq.evaluate(&m_inf_norm_setup.decomposed[i], &alpha));
        }
        let m_inf_norm_decomposed_eval_pf = self.celpc_prover.evaluate_batch(
            &alpha,
            &alpha_combine,
            &m_inf_norm_decomposed_eval,
            &m_inf_norm_setup.decomposed_oracles.commitment,
        );
        let m_inf_norm_eval_pf = self.arith_check_eval(&alpha, &m_inf_norm_oracle);

        let mut e_inf_norm_decomposed_eval = Vec::with_capacity(e_inf_norm_setup.decomposed.len());
        for i in 0..e_inf_norm_setup.decomposed.len() {
            e_inf_norm_decomposed_eval
                .push(self.ringq.evaluate(&e_inf_norm_setup.decomposed[i], &alpha));
        }
        let e_inf_norm_decomposed_eval_pf = self.celpc_prover.evaluate_batch(
            &alpha,
            &alpha_combine,
            &e_inf_norm_decomposed_eval,
            &e_inf_norm_setup.decomposed_oracles.commitment,
        );
        let e_inf_norm_eval_pf = self.arith_check_eval(&alpha, &e_inf_norm_oracle);

        let aut_eval_pf = self.sum_check_eval(&alpha, &alpha_combine, &aut_poly, &aut_oracle);

        let ntt_eval_pf = self.sum_check_eval(&alpha, &alpha_combine, &ntt_poly, &ntt_oracle);

        let pk_eval_pf = self.arith_check_eval(&alpha, &pk_oracle);

        let rlk_eval_pf = self.arith_check_eval(&alpha, &rlk_oracle);

        let atk_eval_pf = self.arith_check_eval(&alpha, &atk_oracle);

        let cjk_eval_pf = self.arith_check_eval(&alpha, &cjk_oracle);

        let ct_eval_pf = self.arith_check_eval(&alpha, &ct_oracle);

        return CKKSProof {
            ckks_oracle: ckks_oracle,
            ckks_eval_pf: ckks_eval_pf,

            sk_inf_norm_decomposed_oracle: sk_inf_norm_setup.decomposed_oracles,
            sk_inf_norm_decomposed_eval_pf: sk_inf_norm_decomposed_eval_pf,
            sk_inf_norm_oracle: sk_inf_norm_oracle,
            sk_inf_norm_eval_pf: sk_inf_norm_eval_pf,

            sk_two_norm_oracle: sk_two_norm_setup.u_oracle,
            sk_two_norm_eval_pf: sk_two_norm_eval_pf,
            sk_two_norm_arith_oracle: sk_two_norm_arith_oracle,
            sk_two_norm_arith_eval_pf: sk_two_norm_arith_eval_pf,
            sk_two_norm_sum_oracle: sk_two_norm_sumcheck_oracle,
            sk_two_norm_sum_eval_pf: sk_two_norm_sumcheck_eval_pf,

            m_inf_norm_decomposed_oracle: m_inf_norm_setup.decomposed_oracles,
            m_inf_norm_decomposed_eval_pf: m_inf_norm_decomposed_eval_pf,
            m_inf_norm_oracle: m_inf_norm_oracle,
            m_inf_norm_eval_pf: m_inf_norm_eval_pf,

            e_inf_norm_decomposed_oracle: e_inf_norm_setup.decomposed_oracles,
            e_inf_norm_decomposed_eval_pf: e_inf_norm_decomposed_eval_pf,
            e_inf_norm_oracle: e_inf_norm_oracle,
            e_inf_norm_eval_pf: e_inf_norm_eval_pf,

            aut_oracle: aut_oracle,
            aut_eval_pf: aut_eval_pf,

            ntt_oracle: ntt_oracle,
            ntt_proof: ntt_eval_pf,

            pk_oracle: pk_oracle,
            pk_proof: pk_eval_pf,

            rlk_oracle: rlk_oracle,
            rlk_proof: rlk_eval_pf,

            atk_oracle: atk_oracle,
            atk_proof: atk_eval_pf,

            cjk_oracle: cjk_oracle,
            cjk_proof: cjk_eval_pf,

            ct_oracle: ct_oracle,
            ct_proof: ct_eval_pf,
        };
    }
}

pub struct Verifier<'a> {
    pub params: &'a Parameters,

    pub encoder: Encoder<'a>,
    pub celpc_verifier: celpc::PolynomialVerifier<'a>,

    pub oracle: Oracle,

    pub ringq: BigRing,
    pub neg_transformer: rlwe::NegacyclicTransformer,
}

impl<'a> Verifier<'a> {
    pub fn new(params: &'a Parameters, ck: &'a celpc::CommitKey) -> Verifier<'a> {
        let encoder = Encoder::new(params);
        let celpc_verifier = celpc::PolynomialVerifier::new(&params.pcs, ck);

        Verifier {
            params: params,
            encoder: encoder,
            celpc_verifier: celpc_verifier,

            oracle: Oracle::new(),

            ringq: BigRing::new(params.embedding_n, &params.rlwe.q),
            neg_transformer: rlwe::NegacyclicTransformer::new(params.rlwe.n, &params.rlwe.q),
        }
    }

    pub fn sum_check_challenge(
        &mut self,
        sum_check_oracle: &SumCheckOracle,
    ) -> Option<SumCheckChallenge> {
        if !self.celpc_verifier.verify(
            &sum_check_oracle.g_oracle.commitment,
            &sum_check_oracle.g_oracle.open_proof,
        ) {
            return None;
        }
        if !self.celpc_verifier.verify_batch(
            &sum_check_oracle.quo_rem_oracle.commitment,
            &sum_check_oracle.quo_rem_oracle.open_proof,
        ) {
            return None;
        }

        self.oracle
            .write_polynomial_oracle(&sum_check_oracle.g_oracle);
        self.oracle.write_bigint(&sum_check_oracle.mu);
        self.oracle.finalize();

        let beta = self.oracle.read_range_bigint(&self.params.rlwe.q);

        return Some(SumCheckChallenge { beta: beta });
    }

    pub fn sum_check(
        &mut self,
        alpha: &Integer,
        alpha_combine: &Integer,
        c: &PolyMultiVariatePoly,
        ai_eval: &[Integer],
        sum_check_challenge: &SumCheckChallenge,
        sum_check_oracle: &SumCheckOracle,
        sum_check_eval_pf: &SumCheckEvalProof,
    ) -> bool {
        if !self.celpc_verifier.verify_evaluation(
            &alpha,
            &sum_check_oracle.g_oracle.commitment,
            &sum_check_eval_pf.g_eval_pf,
        ) {
            return false;
        }
        if !self.celpc_verifier.verify_evaluation_batch(
            alpha,
            alpha_combine,
            &sum_check_oracle.quo_rem_oracle.commitment,
            &sum_check_eval_pf.quo_rem_eval_pf,
        ) {
            return false;
        }

        let mut c_big = BigMultiVariatePoly {
            coeffs: Vec::with_capacity(c.coeffs.len()),
            max_degree: c.max_degree,
        };
        for i in 0..c.coeffs.len() {
            c_big.coeffs.push((
                self.ringq.evaluate(&c.coeffs[i].0, &alpha),
                c.coeffs[i].1.clone(),
            ));
        }
        let mut check = self.ringq.evaluate_multivariate(&c_big, &ai_eval);
        check *= &sum_check_challenge.beta;
        check += &sum_check_eval_pf.g_eval_pf.y_big;
        check.modulo_mut(&self.params.rlwe.q);

        let mut z = alpha
            .pow_mod_ref(&Integer::from(self.params.rlwe.n), &self.params.rlwe.q)
            .unwrap()
            .complete();
        z -= Integer::ONE;

        let (quo_alpha, rem_alpha) = (
            &sum_check_eval_pf.quo_rem_eval_pf.y_batch[0],
            &sum_check_eval_pf.quo_rem_eval_pf.y_batch[1],
        );
        let mut check_quo_rem = Integer::ZERO;
        check_quo_rem.assign(quo_alpha);
        check_quo_rem *= &z;
        check_quo_rem += rem_alpha;
        check_quo_rem += &sum_check_oracle.mu;
        check_quo_rem.modulo_mut(&self.params.rlwe.q);

        check -= &check_quo_rem;
        if !check.is_zero() {
            return false;
        }

        return true;
    }

    pub fn arith_check(
        &mut self,
        alpha: &Integer,
        c: &PolyMultiVariatePoly,
        ai_eval: &[Integer],
        arith_check_oracle: &ArithCheckOracle,
        arith_check_eval_pf: &ArithCheckEvalProof,
    ) -> bool {
        if !self.celpc_verifier.verify(
            &arith_check_oracle.quo_oracle.commitment,
            &arith_check_oracle.quo_oracle.open_proof,
        ) {
            return false;
        }

        if !self.celpc_verifier.verify_evaluation(
            &alpha,
            &arith_check_oracle.quo_oracle.commitment,
            &arith_check_eval_pf.quo_eval_pf,
        ) {
            return false;
        }

        let mut c_big = BigMultiVariatePoly {
            coeffs: Vec::with_capacity(c.coeffs.len()),
            max_degree: c.max_degree,
        };
        for i in 0..c.coeffs.len() {
            c_big.coeffs.push((
                self.ringq.evaluate(&c.coeffs[i].0, &alpha),
                c.coeffs[i].1.clone(),
            ));
        }

        let mut check = self.ringq.evaluate_multivariate(&c_big, &ai_eval);

        let mut z = alpha
            .pow_mod_ref(&Integer::from(self.params.rlwe.n), &self.params.rlwe.q)
            .unwrap()
            .complete();
        z -= Integer::ONE;

        let mut check_quo = Integer::ZERO;
        check_quo.assign(&z);
        check_quo *= &arith_check_eval_pf.quo_eval_pf.y_big;
        check_quo.modulo_mut(&self.params.rlwe.q);

        check -= &check_quo;
        if !check.is_zero() {
            return false;
        }

        return true;
    }

    pub fn lin_check_circuit(&mut self, lin_type: &[LinCheckType]) -> PolyMultiVariatePoly {
        return lin_check_circuit(
            &mut self.oracle,
            &mut self.neg_transformer,
            &self.encoder,
            lin_type,
        );
    }

    pub fn inf_norm_check(
        &mut self,
        alpha: &Integer,
        decomposed_oracle: &BatchPolynomialOracle,
        decomposed_eval: &[Integer],
        arith_check_oracle: &ArithCheckOracle,
        arith_check_eval_pf: &ArithCheckEvalProof,
        log_bound: usize,
    ) -> bool {
        let input_len = decomposed_eval.len() / (log_bound + 2);

        self.oracle
            .write_batch_polynomial_oracle(&decomposed_oracle);
        self.oracle.finalize();

        let beta = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let gamma = self.oracle.read_range_bigint(&self.params.rlwe.q);

        let inf_norm_circuit =
            inf_norm_check_circuit(&self.encoder, &beta, &gamma, input_len, log_bound + 1);

        return self.arith_check(
            &alpha,
            &inf_norm_circuit,
            &decomposed_eval,
            &arith_check_oracle,
            &arith_check_eval_pf,
        );
    }

    pub fn two_norm_check_circuit(
        &mut self,
        log_bound: usize,
    ) -> (PolyMultiVariatePoly, PolyMultiVariatePoly) {
        let mut base_neg = vec![Integer::ZERO; self.params.rlwe.n];
        base_neg[0].assign(-1);
        for i in 0..2 * log_bound {
            base_neg[i + 1].assign(-(1 << i));
        }
        let mut c_neg = vec![Integer::ZERO; self.params.rlwe.n];
        for i in 0..2 * log_bound + 1 {
            c_neg[i].assign(-1);
        }

        let base_neg_ecd = self.encoder.encode(&base_neg);
        let c_neg_ecd = self.encoder.encode(&c_neg);
        let one_ecd = self
            .encoder
            .encode(&vec![Integer::from(1); self.params.rlwe.n]);

        let arith_circuit = PolyMultiVariatePoly {
            coeffs: vec![(one_ecd.clone(), vec![2]), (c_neg_ecd, vec![1])],
            max_degree: 2,
        };
        let sum_circuit = PolyMultiVariatePoly {
            coeffs: vec![(one_ecd.clone(), vec![1, 0]), (base_neg_ecd, vec![0, 1])],
            max_degree: 1,
        };

        return (arith_circuit, sum_circuit);
    }

    pub fn prove_ckks(
        &mut self,
        cts: &[rlwe::Ciphertext],
        pk: &rlwe::PublicKey,
        rlk: &rlwe::RelinKey,
        atk: &rlwe::AutomorphismKey,
        cjk: &rlwe::AutomorphismKey,
        ckks_pf: &CKKSProof,
    ) -> bool {
        let level = self.params.rlwe.gadget.len();
        let ct_count = cts.len();

        let s_coeffs_eval = ckks_pf.ckks_eval_pf.y_batch[0].clone();
        let s_ntt_eval = ckks_pf.ckks_eval_pf.y_batch[1].clone();
        let satk_ntt_eval = ckks_pf.ckks_eval_pf.y_batch[2].clone();
        let scjk_ntt_eval = ckks_pf.ckks_eval_pf.y_batch[3].clone();
        let epk_coeffs_eval = ckks_pf.ckks_eval_pf.y_batch[4].clone();
        let epk_ntt_eval = ckks_pf.ckks_eval_pf.y_batch[5].clone();
        let mut erlk_coeffs_eval = vec![Integer::ZERO; level];
        let mut erlk_ntt_eval = vec![Integer::ZERO; level];
        let mut eatk_coeffs_eval = vec![Integer::ZERO; level];
        let mut eatk_ntt_eval = vec![Integer::ZERO; level];
        let mut ecjk_coeffs_eval = vec![Integer::ZERO; level];
        let mut ecjk_ntt_eval = vec![Integer::ZERO; level];
        for i in 0..level {
            erlk_coeffs_eval[i] = ckks_pf.ckks_eval_pf.y_batch[6 + 6 * i].clone();
            erlk_ntt_eval[i] = ckks_pf.ckks_eval_pf.y_batch[7 + 6 * i].clone();
            eatk_coeffs_eval[i] = ckks_pf.ckks_eval_pf.y_batch[8 + 6 * i].clone();
            eatk_ntt_eval[i] = ckks_pf.ckks_eval_pf.y_batch[9 + 6 * i].clone();
            ecjk_coeffs_eval[i] = ckks_pf.ckks_eval_pf.y_batch[10 + 6 * i].clone();
            ecjk_ntt_eval[i] = ckks_pf.ckks_eval_pf.y_batch[11 + 6 * i].clone();
        }
        let mut m_coeffs_eval = vec![Integer::ZERO; ct_count];
        let mut m_ntt_eval = vec![Integer::ZERO; ct_count];
        let mut ect_coeffs_eval = vec![Integer::ZERO; ct_count];
        let mut ect_ntt_eval = vec![Integer::ZERO; ct_count];
        for i in 0..ct_count {
            m_coeffs_eval[i] = ckks_pf.ckks_eval_pf.y_batch[6 + 6 * level + 4 * i].clone();
            m_ntt_eval[i] = ckks_pf.ckks_eval_pf.y_batch[7 + 6 * level + 4 * i].clone();
            ect_coeffs_eval[i] = ckks_pf.ckks_eval_pf.y_batch[8 + 6 * level + 4 * i].clone();
            ect_ntt_eval[i] = ckks_pf.ckks_eval_pf.y_batch[9 + 6 * level + 4 * i].clone();
        }

        if !self.celpc_verifier.verify_batch(
            &ckks_pf.ckks_oracle.commitment,
            &ckks_pf.ckks_oracle.open_proof,
        ) {
            return false;
        }

        self.oracle
            .write_batch_polynomial_oracle(&ckks_pf.ckks_oracle);
        self.oracle.finalize();

        let gamma = self.oracle.read_range_bigint(&self.params.rlwe.q);

        let sk_two_norm_chal = match self.sum_check_challenge(&ckks_pf.sk_two_norm_sum_oracle) {
            Some(c) => c,
            None => return false,
        };

        let aut_chal = match self.sum_check_challenge(&ckks_pf.aut_oracle) {
            Some(c) => c,
            None => return false,
        };

        let ntt_chal = match self.sum_check_challenge(&ckks_pf.ntt_oracle) {
            Some(c) => c,
            None => return false,
        };

        self.oracle
            .write_arithcheck_oracle(&ckks_pf.sk_inf_norm_oracle);
        self.oracle
            .write_arithcheck_oracle(&ckks_pf.sk_two_norm_arith_oracle);
        self.oracle
            .write_sumcheck_oracle(&ckks_pf.sk_two_norm_sum_oracle);
        self.oracle
            .write_arithcheck_oracle(&ckks_pf.m_inf_norm_oracle);
        self.oracle
            .write_arithcheck_oracle(&ckks_pf.e_inf_norm_oracle);
        self.oracle.write_sumcheck_oracle(&ckks_pf.aut_oracle);
        self.oracle.write_sumcheck_oracle(&ckks_pf.ntt_oracle);
        self.oracle.write_arithcheck_oracle(&ckks_pf.pk_oracle);
        self.oracle.write_arithcheck_oracle(&ckks_pf.rlk_oracle);
        self.oracle.write_arithcheck_oracle(&ckks_pf.atk_oracle);
        self.oracle.write_arithcheck_oracle(&ckks_pf.cjk_oracle);
        self.oracle.write_arithcheck_oracle(&ckks_pf.ct_oracle);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &ckks_pf.ckks_oracle.commitment,
            &ckks_pf.ckks_eval_pf,
        ) {
            println!("CKKS evaluation verification failed");
            return false;
        }

        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &ckks_pf.sk_inf_norm_decomposed_oracle.commitment,
            &ckks_pf.sk_inf_norm_decomposed_eval_pf,
        ) {
            println!("SK inf norm evaluation verification failed");
            return false;
        }

        if !self.inf_norm_check(
            &alpha,
            &ckks_pf.sk_inf_norm_decomposed_oracle,
            &ckks_pf.sk_inf_norm_decomposed_eval_pf.y_batch,
            &ckks_pf.sk_inf_norm_oracle,
            &ckks_pf.sk_inf_norm_eval_pf,
            0,
        ) {
            println!("SK inf norm check failed");
            return false;
        }

        if !self.celpc_verifier.verify_evaluation(
            &alpha,
            &ckks_pf.sk_two_norm_oracle.commitment,
            &ckks_pf.sk_two_norm_eval_pf,
        ) {
            println!("SK two norm evaluation verification failed");
            return false;
        }

        let (sk_two_norm_arith_circuit, sk_two_norm_sumcheck_circuit) =
            self.two_norm_check_circuit(self.params.rlwe.s_hamming_weight.ilog2() as usize);

        if !self.arith_check(
            &alpha,
            &sk_two_norm_arith_circuit,
            &[ckks_pf.sk_two_norm_eval_pf.y_big.clone()],
            &ckks_pf.sk_two_norm_arith_oracle,
            &ckks_pf.sk_two_norm_arith_eval_pf,
        ) {
            println!("SK two norm arith check failed");
            return false;
        }
        if !self.sum_check(
            &alpha,
            &alpha_combine,
            &sk_two_norm_sumcheck_circuit,
            &[
                s_coeffs_eval.clone(),
                ckks_pf.sk_two_norm_eval_pf.y_big.clone(),
            ],
            &sk_two_norm_chal,
            &ckks_pf.sk_two_norm_sum_oracle,
            &ckks_pf.sk_two_norm_sum_eval_pf,
        ) {
            println!("SK two norm sum check failed");
            return false;
        }

        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &ckks_pf.m_inf_norm_decomposed_oracle.commitment,
            &ckks_pf.m_inf_norm_decomposed_eval_pf,
        ) {
            println!("M inf norm evaluation verification failed");
            return false;
        }
        if !self.inf_norm_check(
            &alpha,
            &ckks_pf.m_inf_norm_decomposed_oracle,
            &ckks_pf.m_inf_norm_decomposed_eval_pf.y_batch,
            &ckks_pf.m_inf_norm_oracle,
            &ckks_pf.m_inf_norm_eval_pf,
            cts[0].m_log_bound,
        ) {
            println!("M inf norm check failed");
            return false;
        }

        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &ckks_pf.e_inf_norm_decomposed_oracle.commitment,
            &ckks_pf.e_inf_norm_decomposed_eval_pf,
        ) {
            println!("E inf norm evaluation verification failed");
            return false;
        }

        if !self.inf_norm_check(
            &alpha,
            &ckks_pf.e_inf_norm_decomposed_oracle,
            &ckks_pf.e_inf_norm_decomposed_eval_pf.y_batch,
            &ckks_pf.e_inf_norm_oracle,
            &ckks_pf.e_inf_norm_eval_pf,
            self.params.rlwe.log_e_bound,
        ) {
            println!("E inf norm check failed");
            return false;
        }

        let aut_circuit = self.lin_check_circuit(&[
            LinCheckType::Automorphism(atk.d),
            LinCheckType::Automorphism(cjk.d),
        ]);
        if !self.sum_check(
            &alpha,
            &alpha_combine,
            &aut_circuit,
            &[
                s_ntt_eval.clone(),
                s_ntt_eval.clone(),
                satk_ntt_eval.clone(),
                scjk_ntt_eval.clone(),
            ],
            &aut_chal,
            &ckks_pf.aut_oracle,
            &ckks_pf.aut_eval_pf,
        ) {
            println!("Automorphism check failed");
            return false;
        }

        // s, m, eck, epk, erlk, eatk, ecjk
        let ntt_check_len = 2 + 2 * ct_count + 3 * level;
        let ntt_circuit = self.lin_check_circuit(&vec![LinCheckType::NTT; ntt_check_len]);
        let mut ntt_check_eval = Vec::with_capacity(ntt_check_len * 2);
        ntt_check_eval.push(s_coeffs_eval.clone());
        ntt_check_eval.push(epk_coeffs_eval.clone());
        for i in 0..ct_count {
            ntt_check_eval.push(m_coeffs_eval[i].clone());
            ntt_check_eval.push(ect_coeffs_eval[i].clone());
        }
        for i in 0..level {
            ntt_check_eval.push(erlk_coeffs_eval[i].clone());
            ntt_check_eval.push(eatk_coeffs_eval[i].clone());
            ntt_check_eval.push(ecjk_coeffs_eval[i].clone());
        }
        ntt_check_eval.push(s_ntt_eval.clone());
        ntt_check_eval.push(epk_ntt_eval.clone());
        for i in 0..ct_count {
            ntt_check_eval.push(m_ntt_eval[i].clone());
            ntt_check_eval.push(ect_ntt_eval[i].clone());
        }
        for i in 0..level {
            ntt_check_eval.push(erlk_ntt_eval[i].clone());
            ntt_check_eval.push(eatk_ntt_eval[i].clone());
            ntt_check_eval.push(ecjk_ntt_eval[i].clone());
        }

        if !self.sum_check(
            &alpha,
            &alpha_combine,
            &ntt_circuit,
            &ntt_check_eval,
            &ntt_chal,
            &ckks_pf.ntt_oracle,
            &ckks_pf.ntt_proof,
        ) {
            println!("NTT check failed");
            return false;
        }

        let neg_one = self.params.rlwe.q.clone() - Integer::ONE;
        let pk0_ntt_ecd = self.encoder.encode(&pk.b_ntt);
        let pk1_ntt_ecd = self.encoder.encode(&pk.a_ntt);
        let neg_one_ecd = self
            .encoder
            .encode(&vec![neg_one.clone(); self.params.rlwe.n]);
        let pk_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (pk0_ntt_ecd, vec![0, 0]),
                (pk1_ntt_ecd, vec![1, 0]),
                (neg_one_ecd, vec![0, 1]),
            ],
            max_degree: 1,
        };
        if !self.arith_check(
            &alpha,
            &pk_circuit,
            &[s_ntt_eval.clone(), epk_ntt_eval.clone()],
            &ckks_pf.pk_oracle,
            &ckks_pf.pk_proof,
        ) {
            println!("PK check failed");
            return false;
        }

        let mut gamma_pow_neg = vec![Integer::ZERO; usize::max(level, ct_count)];
        gamma_pow_neg[0] = neg_one.clone();
        for i in 1..gamma_pow_neg.len() {
            gamma_pow_neg[i] = gamma_pow_neg[i - 1].clone();
            gamma_pow_neg[i] *= &gamma;
            gamma_pow_neg[i].modulo_mut(&self.params.rlwe.q);
        }

        let mut gamma_pow_neg_ecd = Vec::with_capacity(gamma_pow_neg.len());
        for i in 0..gamma_pow_neg.len() {
            gamma_pow_neg_ecd.push(
                self.encoder
                    .encode(&vec![gamma_pow_neg[i].clone(); self.params.rlwe.n]),
            );
        }

        let mut rlk0 = vec![Integer::from(0); self.params.rlwe.n];
        let mut rlk1 = vec![Integer::from(0); self.params.rlwe.n];
        let mut atk0 = vec![Integer::from(0); self.params.rlwe.n];
        let mut atk1 = vec![Integer::from(0); self.params.rlwe.n];
        let mut cjk0 = vec![Integer::from(0); self.params.rlwe.n];
        let mut cjk1 = vec![Integer::from(0); self.params.rlwe.n];
        let mut gad = vec![Integer::from(0); self.params.rlwe.n];
        for i in (0..level).rev() {
            for j in 0..self.params.rlwe.n {
                rlk0[j] *= &gamma;
                rlk0[j] += &rlk.b_ntt[i][j];
                rlk0[j].modulo_mut(&self.params.rlwe.q);

                rlk1[j] *= &gamma;
                rlk1[j] += &rlk.a_ntt[i][j];
                rlk1[j].modulo_mut(&self.params.rlwe.q);

                atk0[j] *= &gamma;
                atk0[j] += &atk.b_ntt[i][j];
                atk0[j].modulo_mut(&self.params.rlwe.q);

                atk1[j] *= &gamma;
                atk1[j] += &atk.a_ntt[i][j];
                atk1[j].modulo_mut(&self.params.rlwe.q);

                cjk0[j] *= &gamma;
                cjk0[j] += &cjk.b_ntt[i][j];
                cjk0[j].modulo_mut(&self.params.rlwe.q);

                cjk1[j] *= &gamma;
                cjk1[j] += &cjk.a_ntt[i][j];
                cjk1[j].modulo_mut(&self.params.rlwe.q);

                gad[j] *= &gamma;
                gad[j] -= &self.params.rlwe.gadget[i];
                gad[j].modulo_mut(&self.params.rlwe.q);
            }
        }
        let mut ct0 = vec![Integer::from(0); self.params.rlwe.n];
        let mut ct1 = vec![Integer::from(0); self.params.rlwe.n];
        for i in (0..ct_count).rev() {
            for j in 0..self.params.rlwe.n {
                ct0[j] *= &gamma;
                ct0[j] += &cts[i].b_ntt[j];
                ct0[j].modulo_mut(&self.params.rlwe.q);

                ct1[j] *= &gamma;
                ct1[j] += &cts[i].a_ntt[j];
                ct1[j].modulo_mut(&self.params.rlwe.q);
            }
        }

        let rlk0_ecd = self.encoder.encode(&rlk0);
        let rlk1_ecd = self.encoder.encode(&rlk1);
        let atk0_ecd = self.encoder.encode(&atk0);
        let atk1_ecd = self.encoder.encode(&atk1);
        let cjk0_ecd = self.encoder.encode(&cjk0);
        let cjk1_ecd = self.encoder.encode(&cjk1);
        let gad_ecd = self.encoder.encode(&gad);
        let ct0_ecd = self.encoder.encode(&ct0);
        let ct1_ecd = self.encoder.encode(&ct1);

        let mut rlk_circuit = PolyMultiVariatePoly {
            coeffs: Vec::with_capacity(level + 1),
            max_degree: 2,
        };
        let mut deg = vec![0; level + 1];
        rlk_circuit.coeffs.push((rlk0_ecd, deg.clone()));
        deg.fill(0);
        deg[0] = 1;
        rlk_circuit.coeffs.push((rlk1_ecd, deg.clone()));
        deg.fill(0);
        deg[0] = 2;
        rlk_circuit.coeffs.push((gad_ecd.clone(), deg.clone()));
        for j in 0..level {
            deg.fill(0);
            deg[j + 1] = 1;
            rlk_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[j].clone(), deg.clone()));
        }

        let mut atk_circuit = PolyMultiVariatePoly {
            coeffs: Vec::with_capacity(level + 2),
            max_degree: 1,
        };
        let mut cjk_circuit = PolyMultiVariatePoly {
            coeffs: Vec::with_capacity(level + 2),
            max_degree: 1,
        };
        deg = vec![0; level + 2];
        atk_circuit.coeffs.push((atk0_ecd, deg.clone()));
        cjk_circuit.coeffs.push((cjk0_ecd, deg.clone()));
        deg.fill(0);
        deg[0] = 1;
        atk_circuit.coeffs.push((atk1_ecd, deg.clone()));
        cjk_circuit.coeffs.push((cjk1_ecd, deg.clone()));
        deg.fill(0);
        deg[1] = 1;
        atk_circuit.coeffs.push((gad_ecd.clone(), deg.clone()));
        cjk_circuit.coeffs.push((gad_ecd.clone(), deg.clone()));
        for j in 0..level {
            deg.fill(0);
            deg[j + 2] = 1;
            atk_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[j].clone(), deg.clone()));
            cjk_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[j].clone(), deg.clone()));
        }

        let mut ct_circuit = PolyMultiVariatePoly {
            coeffs: Vec::with_capacity(ct_count * 2 + 1),
            max_degree: 1,
        };
        deg = vec![0; ct_count * 2 + 1];
        ct_circuit.coeffs.push((ct0_ecd, deg.clone()));
        deg[0] = 1;
        ct_circuit.coeffs.push((ct1_ecd, deg.clone()));
        for i in 0..ct_count {
            deg.fill(0);
            deg[i * 2 + 1] = 1;
            ct_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[i].clone(), deg.clone()));
            deg.fill(0);
            deg[i * 2 + 2] = 1;
            ct_circuit
                .coeffs
                .push((gamma_pow_neg_ecd[i].clone(), deg.clone()));
        }

        let mut rlk_check_inputs_eval = Vec::with_capacity(level + 1);
        rlk_check_inputs_eval.push(s_ntt_eval.clone());
        for i in 0..level {
            rlk_check_inputs_eval.push(erlk_ntt_eval[i].clone());
        }
        if !self.arith_check(
            &alpha,
            &rlk_circuit,
            &rlk_check_inputs_eval,
            &ckks_pf.rlk_oracle,
            &ckks_pf.rlk_proof,
        ) {
            println!("RLK check failed");
            return false;
        }

        let mut atk_check_inputs_eval = Vec::with_capacity(level + 2);
        atk_check_inputs_eval.push(s_ntt_eval.clone());
        atk_check_inputs_eval.push(satk_ntt_eval.clone());
        for i in 0..level {
            atk_check_inputs_eval.push(eatk_ntt_eval[i].clone());
        }
        if !self.arith_check(
            &alpha,
            &atk_circuit,
            &atk_check_inputs_eval,
            &ckks_pf.atk_oracle,
            &ckks_pf.atk_proof,
        ) {
            println!("ATK check failed");
            return false;
        }

        let mut cjk_check_inputs_eval = Vec::with_capacity(level + 2);
        cjk_check_inputs_eval.push(s_ntt_eval.clone());
        cjk_check_inputs_eval.push(scjk_ntt_eval.clone());
        for i in 0..level {
            cjk_check_inputs_eval.push(ecjk_ntt_eval[i].clone());
        }
        if !self.arith_check(
            &alpha,
            &cjk_circuit,
            &cjk_check_inputs_eval,
            &ckks_pf.cjk_oracle,
            &ckks_pf.cjk_proof,
        ) {
            println!("CJK check failed");
            return false;
        }

        let mut ct_check_inputs_eval = Vec::with_capacity(ct_count * 2 + 1);
        ct_check_inputs_eval.push(s_ntt_eval.clone());
        for i in 0..ct_count {
            ct_check_inputs_eval.push(m_ntt_eval[i].clone());
            ct_check_inputs_eval.push(ect_ntt_eval[i].clone());
        }
        if !self.arith_check(
            &alpha,
            &ct_circuit,
            &ct_check_inputs_eval,
            &ckks_pf.ct_oracle,
            &ckks_pf.ct_proof,
        ) {
            println!("CT check failed");
            return false;
        }

        return true;
    }
}
