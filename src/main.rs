#![allow(non_snake_case)]

use std::time::Instant;

use ckks_piop::{celpc, rlwe, *};

fn main() {
    let params = Parameters::log_n_14_pk();
    println!("LogN: {}", params.rlwe.n.ilog2());
    println!("Logn: {}", params.pcs.n.ilog2());
    println!("Log Q: {}", params.rlwe.q.significant_bits());

    let ck = celpc::CommitKey::new(&params.pcs, &[0, 0, 0, 0]);

    let now = Instant::now();
    let mut prover = Prover::new(&params, &ck);
    println!("new_prover: {:?}", now.elapsed());

    let now = Instant::now();
    let mut verifier = Verifier::new(&params, &ck);
    println!("new_verifier: {:?}", now.elapsed());

    let ct_count = 1;
    let mut cts = Vec::with_capacity(ct_count);

    let mut kg = rlwe::KeyGenerator::new(&params.rlwe);
    let m_coeffs = vec![rug::Integer::from(1 << 7); params.rlwe.n];
    let mut m_ntt = m_coeffs.clone();
    kg.transformer.ntt(&mut m_ntt);

    let now = Instant::now();
    let sk = kg.gen_secret_key();
    for _ in 0..ct_count {
        cts.push(kg.gen_encryption(&sk, &m_ntt, 16));
    }
    let pk = kg.gen_public_key(&sk);
    let rlk = kg.gen_relin_key(&sk);
    let atk = kg.gen_aut_key(&sk, 5);
    let cjk = kg.gen_aut_key(&sk, 2 * params.rlwe.n - 1);
    println!("keygen: {:?}", now.elapsed());

    let now = Instant::now();
    let ckks_pf = prover.prove_ckks(&cts, &sk, &pk, &rlk, &atk, &cjk);
    println!("prove_ckks: {:?}", now.elapsed());

    let now = Instant::now();
    let ckks_vf = verifier.prove_ckks(&cts, &pk, &rlk, &atk, &cjk, &ckks_pf);
    println!("verify_ckks: {:?}", now.elapsed());
    println!("CKKS: {:?}", ckks_vf);
}
