use crate::csprng::UniformSampler;

use super::{NegacyclicTransformer, Parameters};
use rand::{seq::SliceRandom, thread_rng};
use rug::{Assign, Integer};

pub struct SecretKey {
    pub coeffs: Vec<Integer>,
    pub ntt: Vec<Integer>,
}

pub struct Ciphertext {
    pub a_coeffs: Vec<Integer>,
    pub a_ntt: Vec<Integer>,

    pub b_coeffs: Vec<Integer>,
    pub b_ntt: Vec<Integer>,

    pub m_coeffs: Vec<Integer>,
    pub m_ntt: Vec<Integer>,
    pub m_log_bound: usize,

    pub e_coeffs: Vec<Integer>,
    pub e_ntt: Vec<Integer>,
}

pub struct PublicKey {
    pub a_coeffs: Vec<Integer>,
    pub a_ntt: Vec<Integer>,

    pub b_coeffs: Vec<Integer>,
    pub b_ntt: Vec<Integer>,

    pub epk_coeffs: Vec<Integer>,
    pub epk_ntt: Vec<Integer>,
}

pub struct RelinKey {
    pub a_coeffs: Vec<Vec<Integer>>,
    pub a_ntt: Vec<Vec<Integer>>,

    pub b_coeffs: Vec<Vec<Integer>>,
    pub b_ntt: Vec<Vec<Integer>>,

    pub erlk_coeffs: Vec<Vec<Integer>>,
    pub erlk_ntt: Vec<Vec<Integer>>,

    pub srlk_coeffs: Vec<Integer>,
    pub srlk_ntt: Vec<Integer>,
}

pub struct AutomorphismKey {
    pub a_coeffs: Vec<Vec<Integer>>,
    pub a_ntt: Vec<Vec<Integer>>,

    pub b_coeffs: Vec<Vec<Integer>>,
    pub b_ntt: Vec<Vec<Integer>>,

    pub eatk_coeffs: Vec<Vec<Integer>>,
    pub eatk_ntt: Vec<Vec<Integer>>,

    pub satk_coeffs: Vec<Integer>,
    pub satk_ntt: Vec<Integer>,

    pub d: usize,
}

pub struct KeyGenerator<'a> {
    pub params: &'a Parameters,

    pub uniform_sampler: UniformSampler,
    pub transformer: NegacyclicTransformer,
}

impl<'a> KeyGenerator<'a> {
    pub fn new(params: &'a Parameters) -> Self {
        Self {
            params: params,
            uniform_sampler: UniformSampler::new(),
            transformer: NegacyclicTransformer::new(params.n, &params.q),
        }
    }

    /// Generates the secret key.
    pub fn gen_secret_key(&mut self) -> SecretKey {
        let mut sk = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.s_hamming_weight {
            sk[i] = Integer::from(1);
        }
        sk.shuffle(&mut thread_rng());

        let mut sk_ntt = sk.clone();
        self.transformer.ntt(&mut sk_ntt);

        return SecretKey {
            coeffs: sk,
            ntt: sk_ntt,
        };
    }

    pub fn gen_encryption(
        &mut self,
        sk: &SecretKey,
        m_ntt: &[Integer],
        m_log_bound: usize,
    ) -> Ciphertext {
        let mut a = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            a[i] = self.uniform_sampler.sample_range_bigint(&self.params.q);
        }
        let mut a_ntt = a.clone();
        self.transformer.ntt(&mut a_ntt);

        let mut e = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            e[i] = Integer::from(
                (self
                    .uniform_sampler
                    .sample_range((1 << (self.params.log_e_bound + 1)) + 1)
                    as i64)
                    - (1 << self.params.log_e_bound as i64),
            );
        }
        let mut e_ntt = e.clone();
        self.transformer.ntt(&mut e_ntt);

        let m_ntt = m_ntt.to_vec();
        let mut m_coeffs = m_ntt.clone();
        self.transformer.intt(&mut m_coeffs);

        let mut b_ntt = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            b_ntt[i].assign(-&a_ntt[i]);
            b_ntt[i] *= &sk.ntt[i];
            b_ntt[i] += &e_ntt[i];
            b_ntt[i] += &m_ntt[i];
            b_ntt[i].modulo_mut(&self.params.q);
        }
        let mut b = b_ntt.clone();
        self.transformer.intt(&mut b);

        return Ciphertext {
            a_coeffs: a,
            a_ntt: a_ntt,

            b_coeffs: b,
            b_ntt: b_ntt,

            m_coeffs: m_coeffs,
            m_ntt: m_ntt,
            m_log_bound: m_log_bound,

            e_coeffs: e,
            e_ntt,
        };
    }

    pub fn gen_public_key(&mut self, sk: &SecretKey) -> PublicKey {
        let pk = self.gen_encryption(sk, &vec![Integer::ZERO; self.params.n], 0);
        return PublicKey {
            a_coeffs: pk.a_coeffs,
            a_ntt: pk.a_ntt,

            b_coeffs: pk.b_coeffs,
            b_ntt: pk.b_ntt,

            epk_coeffs: pk.e_coeffs,
            epk_ntt: pk.e_ntt,
        };
    }

    /// Generates the relinearization key.
    pub fn gen_relin_key(&mut self, sk: &SecretKey) -> RelinKey {
        let mut sk_sq_ntt = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            sk_sq_ntt[i].assign(&sk.ntt[i]);
            sk_sq_ntt[i] *= &sk.ntt[i];
            sk_sq_ntt[i].modulo_mut(&self.params.q);
        }
        let mut sk_sq = sk_sq_ntt.clone();
        self.transformer.intt(&mut sk_sq);

        let level = self.params.gadget.len();

        let mut a_coeffs = Vec::with_capacity(level);
        let mut a_ntt = Vec::with_capacity(level);

        let mut b_coeffs = Vec::with_capacity(level);
        let mut b_ntt = Vec::with_capacity(level);

        let mut erlk_coeffs = Vec::with_capacity(level);
        let mut erlk_ntt = Vec::with_capacity(level);

        for i in 0..level {
            let mut g_sk_sq_ntt = sk_sq_ntt.clone();
            for j in 0..self.params.n {
                g_sk_sq_ntt[j] *= &self.params.gadget[i];
                g_sk_sq_ntt[j].modulo_mut(&self.params.q);
            }
            let ct = self.gen_encryption(sk, &g_sk_sq_ntt, 0);

            a_coeffs.push(ct.a_coeffs);
            a_ntt.push(ct.a_ntt);

            b_coeffs.push(ct.b_coeffs);
            b_ntt.push(ct.b_ntt);

            erlk_coeffs.push(ct.e_coeffs);
            erlk_ntt.push(ct.e_ntt);
        }

        return RelinKey {
            a_coeffs: a_coeffs,
            a_ntt: a_ntt,

            b_coeffs: b_coeffs,
            b_ntt: b_ntt,

            erlk_coeffs: erlk_coeffs,
            erlk_ntt: erlk_ntt,

            srlk_coeffs: sk_sq,
            srlk_ntt: sk_sq_ntt,
        };
    }

    /// Generates the automorphism key.
    pub fn gen_aut_key(&mut self, sk: &SecretKey, d: usize) -> AutomorphismKey {
        let level = self.params.gadget.len();

        let sk_aut_ntt = self.transformer.automorphism(&sk.ntt, d);
        let mut sk_aut = sk_aut_ntt.clone();
        self.transformer.intt(&mut sk_aut);

        let mut a_coeffs = Vec::with_capacity(level);
        let mut a_ntt = Vec::with_capacity(level);

        let mut b_coeffs = Vec::with_capacity(level);
        let mut b_ntt = Vec::with_capacity(level);

        let mut eatk_coeffs = Vec::with_capacity(level);
        let mut eatk_ntt = Vec::with_capacity(level);

        for i in 0..level {
            let mut g_sk_aut_ntt = sk_aut_ntt.clone();
            for j in 0..self.params.n {
                g_sk_aut_ntt[j] *= &self.params.gadget[i];
                g_sk_aut_ntt[j].modulo_mut(&self.params.q);
            }
            let ct = self.gen_encryption(sk, &g_sk_aut_ntt, 0);

            a_coeffs.push(ct.a_coeffs);
            a_ntt.push(ct.a_ntt);

            b_coeffs.push(ct.b_coeffs);
            b_ntt.push(ct.b_ntt);

            eatk_coeffs.push(ct.e_coeffs);
            eatk_ntt.push(ct.e_ntt);
        }

        return AutomorphismKey {
            a_coeffs: a_coeffs,
            a_ntt: a_ntt,

            b_coeffs: b_coeffs,
            b_ntt: b_ntt,

            eatk_coeffs: eatk_coeffs,
            eatk_ntt: eatk_ntt,

            satk_coeffs: sk_aut,
            satk_ntt: sk_aut_ntt,

            d: d,
        };
    }
}
