use rug::Integer;

#[derive(Clone)]
pub struct Parameters {
    pub n: usize,
    pub q: Integer,
    pub q_rns: Vec<u64>,
    pub gadget: Vec<Integer>,

    pub s_hamming_weight: usize,
    pub log_e_bound: usize,
}

impl Parameters {
    pub fn new(
        n: usize,
        q: &Integer,
        q_bits: &[usize],
        dnum: usize,
        s_hamming_weight: usize,
        log_e_bound: usize,
    ) -> Self {
        let q_rns_cnt = q_bits.len();
        let mut q_rns = Vec::with_capacity(q_rns_cnt);
        let nn = Integer::from(2 * n);

        for i in 0..q_rns_cnt {
            let mut qq = Integer::from((1u64 << q_bits[i]) + 1);
            loop {
                if q_rns.iter().any(|x| x == &qq.to_u64().unwrap()) {
                    qq += &nn;
                    continue;
                }

                if qq.is_probably_prime(30) != rug::integer::IsPrime::No {
                    q_rns.push(qq.to_u64().unwrap());
                    break;
                }
                qq += &nn;
            }
        }

        let gadget_cnt = q_rns_cnt.div_ceil(dnum);
        let mut gadget = Vec::with_capacity(gadget_cnt);
        let q_chunk = q_rns.chunks(dnum);
        for chunk in q_chunk {
            let mut g = q.clone();
            let mut q_big = Integer::from(1);
            for q in chunk {
                q_big *= q;
            }
            g /= &q_big;
            gadget.push(g);
        }

        Self {
            n: n,
            q: q.clone(),

            q_rns: q_rns,
            gadget: gadget,

            s_hamming_weight: s_hamming_weight,
            log_e_bound: log_e_bound,
        }
    }
}
