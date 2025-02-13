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

    pub fn log_n_14_pk() -> Parameters {
        let celpc_params_literal = celpc::ParametersLiteral {
            q: vec![72057594037948417, 72057594037641217],
            d: 1 << 11,

            mu: 1,
            nu: 2,

            b: 10792,
            r: 32,

            n: 1 << 12,
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

        let bfv_params = rlwe::Parameters::new(1 << 14, &celpc_params.p, 1, 128, 0);

        return Parameters::new(&bfv_params, &celpc_params);
    }

    // pub fn log_n_14_pk_evk() -> Parameters {
    //     let celpc_params_literal = celpc::ParametersLiteral {
    //         q: vec![72057594037948417, 72057594037641217],
    //         d: 1 << 11,

    //         mu: 1,
    //         nu: 2,

    //         b: 10792,
    //         r: 32,

    //         n: 1 << 13,
    //         N: 1 << 14,

    //         s1: 10.0,
    //         s2: 34.0,
    //         s3: 20.0f64.exp2(),

    //         sig1: 20.0,
    //         sig2: 68.0,
    //         sig3: 21.0f64.exp2(),

    //         log_bound_open: 35.4,
    //         log_bound_eval: 52.6,
    //     };
    //     let celpc_params = celpc::Parameters::new(celpc_params_literal);

    //     let bfv_params = rlwe::Parameters::new(1 << 14, &celpc_params.p, 2, 1, 1);

    //     return Parameters::new(&bfv_params, &celpc_params);
    // }

    // pub fn log_n_15_pk() -> Parameters {
    //     let celpc_params_literal = celpc::ParametersLiteral {
    //         q: vec![72057594037948417, 72057594037641217],
    //         d: 1 << 11,

    //         mu: 1,
    //         nu: 2,

    //         b: 11710,
    //         r: 64,

    //         n: 1 << 12,
    //         N: 1 << 15,

    //         s1: 10.0,
    //         s2: 34.0,
    //         s3: 22.0f64.exp2(),

    //         sig1: 20.0,
    //         sig2: 68.0,
    //         sig3: 23.0f64.exp2(),

    //         log_bound_open: 37.0,
    //         log_bound_eval: 55.4,
    //     };
    //     let celpc_params = celpc::Parameters::new(celpc_params_literal);

    //     let bfv_params = rlwe::Parameters::new(1 << 15, &celpc_params.p, 4, 1, 1);

    //     return Parameters::new(&bfv_params, &celpc_params);
    // }

    // pub fn log_n_15_pk_evk() -> Parameters {
    //     let celpc_params_literal = celpc::ParametersLiteral {
    //         q: vec![72057594037948417, 72057594037641217],
    //         d: 1 << 11,

    //         mu: 1,
    //         nu: 2,

    //         b: 11710,
    //         r: 64,

    //         n: 1 << 13,
    //         N: 1 << 15,

    //         s1: 10.0,
    //         s2: 34.0,
    //         s3: 22.0f64.exp2(),

    //         sig1: 20.0,
    //         sig2: 68.0,
    //         sig3: 23.0f64.exp2(),

    //         log_bound_open: 37.0,
    //         log_bound_eval: 55.4,
    //     };
    //     let celpc_params = celpc::Parameters::new(celpc_params_literal);

    //     let bfv_params = rlwe::Parameters::new(1 << 15, &celpc_params.p, 4, 1, 1);

    //     return Parameters::new(&bfv_params, &celpc_params);
    // }
}
