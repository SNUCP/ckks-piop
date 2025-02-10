#[allow(non_snake_case)]
use crate::ring::Ring;
use rug::{ops::Pow, Integer};

#[derive(Clone)]
pub struct ParametersLiteral {
    /// q is the modulus of the ring R_q.
    pub q: Vec<u64>,
    /// d is the degree of the ring R_q.
    pub d: usize,
    /// mu is the size of commitment key A0, and commitment itself.
    pub mu: usize,
    /// nu is the size of commitment key A1.
    pub nu: usize,

    /// b is the base of the message.
    pub b: u64,
    /// r is the length of the digits.
    /// Message modulus p = b^r + 1.
    pub r: usize,

    /// n is the number of messages per commitment.
    pub n: usize,
    /// N is the degree of input polynomial.
    pub N: usize,

    pub s1: f64,
    pub s2: f64,
    pub s3: f64,
    pub sig1: f64,
    pub sig2: f64,
    pub sig3: f64,
    pub log_bound_open: f64,
    pub log_bound_eval: f64,
}

#[derive(Clone)]
pub struct Parameters {
    /// q is the modulus of the ring R_q.
    pub q: Vec<u64>,
    /// d is the degree of the ring R_q.
    pub d: usize,
    /// mu is the size of commitment key A0, and commitment itself.
    pub mu: usize,
    /// nu is the size of commitment key A1.
    pub nu: usize,

    /// ringq is the ring R_q.
    pub ringq: Ring,

    /// b is the base of the message.
    pub b: u64,
    /// r is the length of the digits.
    /// Message modulus p = b^r + 1.
    pub r: usize,
    /// p is the message modulus.
    /// p = b^r + 1.
    pub p: Integer,
    /// s is the number of "slots".
    /// s = d / r.
    pub s: usize,
    /// rep is the number of repetitions.
    /// rep = ceil(lambda / log(2d)).
    pub rep: usize,

    /// n is the number of messages per commitment.
    pub n: usize,
    /// l is the number of ring elements per commitment.
    /// l = rn / d.
    pub l: usize,
    /// m is the number of commitments.
    pub m: usize,
    /// N is the degree of input polynomial.
    /// N = nm.
    pub N: usize,

    pub s1: f64,
    pub s2: f64,
    pub s3: f64,
    pub sig1: f64,
    pub sig2: f64,
    pub sig3: f64,
    pub log_bound_open: f64,
    pub log_bound_eval: f64,
}

impl Parameters {
    pub fn new(pl: ParametersLiteral) -> Parameters {
        let ringq = Ring::new(pl.d as usize, &pl.q);
        return Parameters {
            q: pl.q,
            d: pl.d,
            mu: pl.mu,
            nu: pl.nu,

            ringq: ringq,

            b: pl.b,
            r: pl.r,
            p: Integer::from(pl.b).pow(pl.r as u32) + 1,
            s: pl.d / pl.r,
            rep: (128.0f64 / ((2.0f64 * pl.d as f64).log2())).ceil() as usize,

            n: pl.n,
            l: (pl.n * pl.r) / pl.d,
            N: pl.N,
            m: pl.N / pl.n,

            s1: pl.s1,
            s2: pl.s2,
            s3: pl.s3,
            sig1: pl.sig1,
            sig2: pl.sig2,
            sig3: pl.sig3,

            log_bound_open: pl.log_bound_open,
            log_bound_eval: pl.log_bound_eval,
        };
    }
}
