use crate::{celpc, rlwe};

pub struct Parameters {
    pub rlwe: rlwe::Parameters,
    pub pcs: celpc::Parameters,
    pub embedding_n: usize,
}

impl Parameters {
    pub fn new(bfv: &rlwe::Parameters, pcs: &celpc::Parameters) -> Self {
        Parameters {
            rlwe: bfv.clone(),
            pcs: pcs.clone(),
            embedding_n: bfv.n << 3,
        }
    }

    pub fn log_n_14() -> Parameters {
        let celpc_params_literal = celpc::ParametersLiteral {
            q: vec![72057594037948417, 72057594037641217],
            d: 1 << 11,

            mu: 1,
            nu: 2,

            b: 6304,
            r: 32,

            n: 1 << 13,
            N: 1 << 14,

            s1: 10.0,
            s2: 34.0,
            s3: 20.0f64.exp2(),

            sig1: 20.0,
            sig2: 68.0,
            sig3: 21.0f64.exp2(),

            log_bound_open: 35.4,
            log_bound_eval: 52.6,
        };
        let celpc_params = celpc::Parameters::new(celpc_params_literal);

        let bfv_params = rlwe::Parameters::new(
            1 << 14,
            &celpc_params.p,
            &vec![43, 43, 43, 43, 43, 43, 43, 43, 60], // 43 * 8 + 60
            1,
            256,
            0,
        );

        return Parameters::new(&bfv_params, &celpc_params);
    }
}
