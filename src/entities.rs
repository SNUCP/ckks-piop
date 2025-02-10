use crate::{celpc::*, BigPoly, PolyMultiVariatePoly};
use rug::Integer;

#[derive(Clone)]
pub struct PolynomialOracle {
    pub commitment: PolynomialCommitment,
    pub open_proof: OpenProof,
}

#[derive(Clone)]
pub struct BatchPolynomialOracle {
    pub commitment: BatchPolynomialCommitment,
    pub open_proof: BatchOpenProof,
}

#[derive(Clone)]
pub struct SumCheckPoly {
    pub g: BigPoly,
    pub quo: BigPoly,
    pub rem: BigPoly,
}

#[derive(Clone)]
pub struct SumCheckOracle {
    pub g_oracle: PolynomialOracle,
    pub quo_rem_oracle: BatchPolynomialOracle,

    pub mu: Integer,
}

#[derive(Clone)]
pub struct SumCheckEvalProof {
    pub g_eval_pf: EvaluationProof,
    pub quo_rem_eval_pf: BatchEvaluationProof,
}

#[derive(Clone)]
pub struct SumCheckChallenge {
    pub beta: Integer,
}

#[derive(Clone)]
pub struct ArithCheckPoly {
    pub quo: BigPoly,
}

#[derive(Clone)]
pub struct ArithCheckOracle {
    pub quo_oracle: PolynomialOracle,
}

#[derive(Clone)]
pub struct ArithCheckEvalProof {
    pub quo_eval_pf: EvaluationProof,
}

#[derive(Clone)]
pub struct InfNormSetup {
    pub decomposed: Vec<BigPoly>,
    pub decomposed_ntt: Vec<BigPoly>,
    pub decomposed_oracles: BatchPolynomialOracle,
    pub circuit: PolyMultiVariatePoly,
}

#[derive(Clone)]
pub struct TwoNormSetup {
    pub u: BigPoly,
    pub u_ntt: BigPoly,
    pub u_oracle: PolynomialOracle,

    pub arith_circuit: PolyMultiVariatePoly,
    pub sum_circuit: PolyMultiVariatePoly,
}

#[derive(Clone)]
pub enum LinCheckType {
    NTT,
    Automorphism(usize),
}

#[derive(Clone)]
pub struct CKKSProof {
    pub ckks_oracle: BatchPolynomialOracle,
    pub ckks_eval_pf: BatchEvaluationProof,

    pub sk_inf_norm_decomposed_oracle: BatchPolynomialOracle,
    pub sk_inf_norm_decomposed_eval_pf: BatchEvaluationProof,
    pub sk_inf_norm_oracle: ArithCheckOracle,
    pub sk_inf_norm_eval_pf: ArithCheckEvalProof,

    pub sk_two_norm_oracle: PolynomialOracle,
    pub sk_two_norm_eval_pf: EvaluationProof,
    pub sk_two_norm_arith_oracle: ArithCheckOracle,
    pub sk_two_norm_arith_eval_pf: ArithCheckEvalProof,
    pub sk_two_norm_sum_oracle: SumCheckOracle,
    pub sk_two_norm_sum_eval_pf: SumCheckEvalProof,

    pub m_inf_norm_decomposed_oracle: BatchPolynomialOracle,
    pub m_inf_norm_decomposed_eval_pf: BatchEvaluationProof,
    pub m_inf_norm_oracle: ArithCheckOracle,
    pub m_inf_norm_eval_pf: ArithCheckEvalProof,

    pub e_inf_norm_decomposed_oracle: BatchPolynomialOracle,
    pub e_inf_norm_decomposed_eval_pf: BatchEvaluationProof,
    pub e_inf_norm_oracle: ArithCheckOracle,
    pub e_inf_norm_eval_pf: ArithCheckEvalProof,

    pub aut_oracle: SumCheckOracle,
    pub aut_eval_pf: SumCheckEvalProof,

    pub ntt_oracle: SumCheckOracle,
    pub ntt_proof: SumCheckEvalProof,

    pub pk_oracle: ArithCheckOracle,
    pub pk_proof: ArithCheckEvalProof,

    pub rlk_oracle: ArithCheckOracle,
    pub rlk_proof: ArithCheckEvalProof,

    pub atk_oracle: ArithCheckOracle,
    pub atk_proof: ArithCheckEvalProof,

    pub cjk_oracle: ArithCheckOracle,
    pub cjk_proof: ArithCheckEvalProof,

    pub ct_oracle: ArithCheckOracle,
    pub ct_proof: ArithCheckEvalProof,
}
