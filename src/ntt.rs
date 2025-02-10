use rug::Integer;
use rug::*;

/// bitrev computes the bit-reversal permutation of the given vector in-place.
pub fn bitrev<T>(v: &mut [T]) {
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

/// Generates the root of unity for the given degree and modulus.
pub fn gen_root_of_unity(degree: usize, q: &Integer) -> Integer {
    let mut x = Integer::from(2);
    let mut g = Integer::from(0);
    let t1 = (q - Integer::ONE).complete() / degree;
    let t2 = Integer::from(degree / 2);
    loop {
        if x == *q {
            break;
        }
        x += 1;

        g.assign(&x);
        g.pow_mod_mut(&t1, q).unwrap();
        let gg = g.clone().pow_mod(&t2, q).unwrap();
        if gg != 1 {
            break;
        }
    }

    g
}

pub struct CyclicTransformer {
    pub degree: usize,
    pub modulus: Integer,

    pub tw: Vec<Integer>,
    pub tw_inv: Vec<Integer>,
    pub n_inv: Integer,
}

impl CyclicTransformer {
    pub fn new(degree: usize, moduli: &Integer) -> Self {
        let root = gen_root_of_unity(degree, moduli);
        Self::new_with_root(degree, moduli, &root)
    }

    pub fn new_with_root(degree: usize, modulus: &Integer, root: &Integer) -> Self {
        let mut tw = vec![Integer::new(); degree / 2];
        let mut tw_inv = vec![Integer::new(); degree / 2];

        for i in 0..degree / 2 {
            tw[i] = root.clone().pow_mod(&Integer::from(i), modulus).unwrap();
            tw_inv[i] = root
                .clone()
                .pow_mod(&Integer::from(degree - i), modulus)
                .unwrap();
        }

        let n_inv = Integer::from(degree).invert(modulus).unwrap();

        Self {
            degree: degree,
            modulus: modulus.clone(),

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
                let mut j3 = 0;
                for j in j1..j2 {
                    u.assign(&c[j]);
                    v.assign(&c[j + t]);

                    c[j].assign(&u);
                    c[j] += &v;

                    c[j + t].assign(&u);
                    c[j + t] -= &v;
                    c[j + t] *= &tw[j3];

                    c[j].modulo_mut(&q);
                    c[j + t].modulo_mut(&q);

                    j3 += m;
                }
            }
            m <<= 1;
        }

        bitrev(c);
    }

    /// Compute the inverse NTT of the given vector in-place.
    pub fn intt(&self, c: &mut [Integer]) {
        let n = self.degree;
        let tw_inv = &self.tw_inv;
        let q = &self.modulus;
        let n_inv = &self.n_inv;

        bitrev(c);

        let mut u = Integer::from(0);
        let mut v = Integer::from(0);

        let mut t = 1;
        let mut m = n;
        while m > 1 {
            let mut j1 = 0;
            let h = m >> 1;
            for _ in 0..h {
                let j2 = j1 + t;
                let mut j3 = 0;
                for j in j1..j2 {
                    u.assign(&c[j]);
                    v.assign(&c[j + t]);

                    v *= &tw_inv[j3];

                    c[j].assign(&u);
                    c[j] += &v;
                    c[j + t].assign(&u);
                    c[j + t] -= &v;

                    c[j].modulo_mut(&q);
                    c[j + t].modulo_mut(&q);

                    j3 += h
                }
                j1 += t << 1;
            }
            t <<= 1;
            m >>= 1;
        }

        for i in 0..n {
            c[i] *= n_inv;
            c[i].modulo_mut(&q);
        }
    }
}
