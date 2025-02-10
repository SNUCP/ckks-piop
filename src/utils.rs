use rug;
use rug::Assign;

use crate::celpc;
use crate::csprng;
use crate::entities::*;

impl csprng::Oracle {
    pub fn write_polynomial_commitment(&mut self, pc: &celpc::PolynomialCommitment) {
        pc.eta.iter().flatten().for_each(|p| self.write_poly(p));
        pc.h.iter().flatten().for_each(|p| self.write_poly(p));
        pc.h_commit
            .iter()
            .flatten()
            .for_each(|p| self.write_poly(p));
    }

    pub fn write_polynomial_open_proof(&mut self, open_pf: &celpc::OpenProof) {
        open_pf.ch.iter().flatten().for_each(|p| self.write_poly(p));
        open_pf.t.iter().flatten().for_each(|p| self.write_poly(p));
        open_pf
            .tau
            .iter()
            .flatten()
            .for_each(|p| self.write_poly(p));
    }

    pub fn write_polynomial_oracle(&mut self, oracle: &PolynomialOracle) {
        self.write_polynomial_commitment(&oracle.commitment);
        self.write_polynomial_open_proof(&oracle.open_proof);
    }

    pub fn write_batch_polynomial_oracle(&mut self, oracle: &BatchPolynomialOracle) {
        self.write_polynomial_commitment(&oracle.commitment.poly_commit);
        self.write_polynomial_open_proof(&oracle.open_proof.open_pf);
    }

    pub fn write_sumcheck_oracle(&mut self, sc_oracle: &SumCheckOracle) {
        self.write_polynomial_oracle(&sc_oracle.g_oracle);
        self.write_batch_polynomial_oracle(&sc_oracle.quo_rem_oracle);
        self.write_bigint(&sc_oracle.mu);
    }

    pub fn write_arithcheck_oracle(&mut self, ac_oracle: &ArithCheckOracle) {
        self.write_polynomial_oracle(&ac_oracle.quo_oracle);
    }
}

impl<'a> celpc::PolynomialProver<'a> {
    pub fn gen_poly_oracle(&mut self, coeffs: &[rug::Integer]) -> PolynomialOracle {
        let pc = self.commit(coeffs);
        let open_pf = self.prove(&pc);
        PolynomialOracle {
            commitment: pc,
            open_proof: open_pf,
        }
    }

    pub fn gen_batch_poly_oracle(&mut self, coeffs: &[&[rug::Integer]]) -> BatchPolynomialOracle {
        let pc = self.commit_batch(coeffs);
        let open_pf = self.prove_batch(&pc);
        BatchPolynomialOracle {
            commitment: pc,
            open_proof: open_pf,
        }
    }
}

pub fn signed_decompose(x: &rug::Integer, n: usize) -> Vec<rug::Integer> {
    let mut dcmp = vec![rug::Integer::from(0); n + 1];
    let mut x = x.clone();

    for i in 0..n {
        let b = rug::Integer::from(1) << (n - 1 - i);
        let b_neg = -b.clone();

        if &x >= &b {
            dcmp[i].assign(rug::Integer::from(1));
            x -= &b;
        } else if &x <= &b_neg {
            dcmp[i].assign(rug::Integer::from(-1));
            x += &b;
        }
    }
    let b = rug::Integer::from(1);
    let b_neg = rug::Integer::from(-1);
    if &x >= &b {
        dcmp[n].assign(rug::Integer::from(1));
    } else if &x <= &b_neg {
        dcmp[n].assign(rug::Integer::from(-1));
    }

    dcmp.reverse();

    return dcmp;
}
