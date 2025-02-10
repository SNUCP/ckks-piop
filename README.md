# Buckler: Fast Zero Knowledge Proofs for MGHE Keys & Ciphertexts

You need to install nightly toolchain of rustc to run the code.

```
$ RUSTFLAGS="-C target-cpu=native" cargo run --release
LogN: 14
Logn: 12
gen_key: 258.327267ms
new_prover: 434.695927ms
new_verifier: 402.669869ms
ternary_pk_proof: 26.032651112s
verify_ternary_pk_proof: 2.827723316s
verify_ternary_pk_proof result: true
```
