use std::vec;

use rug::*;

/// bitrev computes the bit-reversal permutation of the given vector in-place.
fn bitrev<T>(v: &mut [T]) {
    let mut bit;
    let mut j = 0;
    for i in 1..v.len() {
        bit = v.len() >> 1;
        while j >= bit {
            j -= bit;
            bit >>= 1;
        }
        j += bit;
        if j > i {
            v.swap(i, j);
        }
    }
}

pub struct NegacyclicTransformer {
    pub degree: usize,
    pub modulus: Integer,

    pub tw: Vec<Integer>,
    pub tw_inv: Vec<Integer>,
    pub n_inv: Integer,
}

impl NegacyclicTransformer {
    pub fn new(degree: usize, moduli: &Integer) -> Self {
        let mut tw = vec![Integer::new(); degree];
        let mut tw_inv = vec![Integer::new(); degree];

        let mut x = Integer::from(2);
        let mut g = Integer::from(0);
        let t1 = (moduli - Integer::ONE).complete() / (2 * degree);
        let t2 = Integer::from(degree);
        loop {
            if x == *moduli {
                break;
            }
            x += 1;

            g.assign(&x);
            g.pow_mod_mut(&t1, moduli).unwrap();
            let gg = g.clone().pow_mod(&t2, moduli).unwrap();
            if gg != 1 {
                break;
            }
        }

        for i in 0..degree {
            tw[i] = g.clone().pow_mod(&Integer::from(i), moduli).unwrap();
            tw_inv[i] = g
                .clone()
                .pow_mod(&Integer::from(2 * degree - i), moduli)
                .unwrap();
        }

        bitrev(&mut tw);
        bitrev(&mut tw_inv);

        let mut n_inv = Integer::from(degree);
        n_inv.invert_mut(moduli).unwrap();

        NegacyclicTransformer {
            degree: degree,
            modulus: moduli.clone(),

            tw: tw,
            tw_inv: tw_inv,
            n_inv: n_inv,
        }
    }

    /// Compute the forward NTT of the given vector in-place.
    pub fn ntt(&self, c: &mut [Integer]) {
        let n = self.degree;
        let tw = &self.tw;
        let q = &self.modulus;

        let mut u = Integer::from(0);
        let mut v = Integer::from(0);

        let mut t = n;
        let mut m = 1;
        while m < n {
            t >>= 1;
            for i in 0..m {
                let j1 = i * t * 2;
                let j2 = j1 + t;
                for j in j1..j2 {
                    u.assign(&c[j]);
                    v.assign(&c[j + t]);

                    v *= &tw[m + i];

                    c[j].assign(&u);
                    c[j] += &v;
                    c[j + t].assign(&u);
                    c[j + t] -= &v;

                    c[j].modulo_mut(&q);
                    c[j + t].modulo_mut(&q);
                }
            }
            m <<= 1;
        }

        bitrev(c);
    }

    /// Compute the inverse NTT of the given vector in-place without normalization.
    pub fn intt_without_normalize(&self, c: &mut [Integer]) {
        let n = self.degree;
        let tw_inv = &self.tw_inv;
        let q = &self.modulus;

        let mut u = Integer::from(0);
        let mut v = Integer::from(0);

        bitrev(c);

        let mut t = 1;
        let mut m = n;
        while m > 1 {
            let mut j1 = 0;
            let h = m >> 1;
            for i in 0..h {
                let j2 = j1 + t;
                for j in j1..j2 {
                    u.assign(&c[j]);
                    v.assign(&c[j + t]);

                    c[j].assign(&u);
                    c[j] += &v;

                    c[j + t].assign(&u);
                    c[j + t] -= &v;
                    c[j + t] *= &tw_inv[h + i];

                    c[j].modulo_mut(&q);
                    c[j + t].modulo_mut(&q);
                }
                j1 += t << 1;
            }
            t <<= 1;
            m >>= 1;
        }
    }

    /// Compute the inverse NTT of the given vector in-place.
    pub fn intt(&self, c: &mut [Integer]) {
        self.intt_without_normalize(c);

        for i in 0..c.len() {
            c[i] *= &self.n_inv;
            c[i].modulo_mut(&self.modulus);
        }
    }

    /// Applies the automorphism X -> X^d.
    pub fn automorphism(&self, c: &[Integer], d: usize) -> Vec<Integer> {
        let n = self.degree;
        let mut cout = vec![Integer::ZERO; n];
        for i in 0..n {
            let mut j = ((2 * i + 1) * d) % (2 * n);
            j = (j - 1) >> 1;
            cout[i].assign(&c[j]);
        }
        return cout;
    }
}
