# CKKS-PIOP

You need to install nightly toolchain of rustc to run the code.

```
$ RUSTFLAGS="-C target-cpu=native" cargo run --release
LogN: 14
Logn: 12
Log Q: 429
new_prover: 419.602996ms
new_verifier: 391.027531ms
keygen: 2.885791583s
prove_ckks: 366.453087052s
verify_ckks: 47.950314227s
CKKS: true
```
