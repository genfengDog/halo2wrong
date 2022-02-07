use super::super::multiopen::{
    EvalAggregator,
    MSMAggregator,
    MPC,
    MPE,
    SPC,
    SPE,
    SchemeItem,
    CommitQuery,
    SingleOpeningProof,
    MultiOpeningProof,
};
use super::super::super::{eval, commit, scalar};
use crate::circuit::ecc::base_field_ecc::{BaseFieldEccChip, BaseFieldEccInstruction};
use crate::circuit::ecc::AssignedPoint;
use crate::WrongExt;
use halo2::arithmetic::{CurveAffine, FieldExt};
use halo2::circuit::Region;
use halo2::plonk::Error;
use halo2arith::main_gate::{five::main_gate::MainGate, CombinationOptionCommon, Term};
use halo2arith::{halo2, AssignedValue, MainGateInstructions};

pub struct ParamsPreprocessed<'a, N: FieldExt> {
    q_m: &'a AssignedPoint<N>,
    q_l: &'a AssignedPoint<N>,
    q_r: &'a AssignedPoint<N>,
    q_o: &'a AssignedPoint<N>,
    q_c: &'a AssignedPoint<N>,
    sigma1: &'a AssignedPoint<N>,
    sigma2: &'a AssignedPoint<N>,
    sigma3: &'a AssignedPoint<N>,
}

pub struct VerifyCommitments<'a, N: FieldExt> {
    a: &'a AssignedPoint<N>,
    b: &'a AssignedPoint<N>,
    c: &'a AssignedPoint<N>,
    z: &'a AssignedPoint<N>,
    tl: &'a AssignedPoint<N>,
    tm: &'a AssignedPoint<N>,
    th: &'a AssignedPoint<N>,
    w_z: &'a AssignedPoint<N>,
    w_zw: &'a AssignedPoint<N>,

}

pub struct VerifyEvals<'a, N: FieldExt> {
    a_xi: &'a AssignedValue<N>,
    b_xi: &'a AssignedValue<N>,
    c_xi: &'a AssignedValue<N>,
    sigma1_xi: &'a AssignedValue<N>,
    sigma2_xi: &'a AssignedValue<N>,
    z_xiw: &'a AssignedValue<N>,
    zh_xi: Option<AssignedValue<N>>,
    l1_xi: Option<AssignedValue<N>>,
    pi_xi: Option<AssignedValue<N>>,
}

pub struct PlonkVerifierParams<'a, C: CurveAffine> {
    l: u32,
    n: u32,
    public_wit: Vec<C::ScalarExt>,
    params: ParamsPreprocessed<'a, C::ScalarExt>,
    commits: VerifyCommitments<'a, C::ScalarExt>,
    evals: VerifyEvals<'a, C::ScalarExt>,
    one: &'a AssignedValue<C::ScalarExt>,
    beta: &'a AssignedValue<C::ScalarExt>,
    gamma: &'a AssignedValue<C::ScalarExt>,
    alpha: &'a AssignedValue<C::ScalarExt>,
    xi: &'a AssignedValue<C::ScalarExt>,
    xi_n: Option<AssignedValue<C::ScalarExt>>,
    u: &'a AssignedValue<C::ScalarExt>,
    v: &'a AssignedValue<C::ScalarExt>,
    k1: &'a AssignedValue<C::ScalarExt>,
    k2: &'a AssignedValue<C::ScalarExt>,
    w: &'a AssignedValue<C::ScalarExt>, //TODO the unit root of 2^n = 1
}

impl<C: CurveAffine> PlonkVerifierParams<'_, C> {
    fn pow_vec(
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        base: &AssignedValue<C::ScalarExt>,
        exponent: u32,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<Vec<AssignedValue<C::ScalarExt>>, Error> {
        let mut ret = vec![];
        let mut curr = base.clone();

        for _ in 0..exponent {
            let next = main_gate.mul2(region, &curr, offset)?;
            ret.push(curr);
            curr = next;
        }

        ret.push(curr);
        Ok(ret)
    }

    fn pow(
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        base: &AssignedValue<C::ScalarExt>,
        exponent: u32,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        assert!(exponent >= 1);

        let mut acc = base.clone();

        let mut second_bit = 1;
        while second_bit <= exponent {
            second_bit <<= 1;
        }
        second_bit >>= 2;

        while second_bit > 0 {
            acc = main_gate.mul2(region, &acc, offset)?;
            if exponent & second_bit == 1 {
                acc = main_gate.mul(region, &acc, base, offset)?;
            }
            second_bit >>= 1;
        }

        Ok(acc)
    }

    fn get_xi_n(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        match &self.xi_n {
            None => {
                let xi_n = self.pow(main_gate, &self.xi, self.n, region, offset)?;
                self.xi_n = Some(xi_n.clone());
                Ok(xi_n.clone())
            }
            Some(xi_n) => Ok(xi_n.clone()),
        }
    }

    fn get_xi_2n(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        let xi_n = self.get_xi_n(main_gate, region, offset)?;

        Ok(main_gate.mul(region, &xi_n, &xi_n, offset)?)
    }

    fn get_zh_xi(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        match &self.evals.zh_xi {
            None => {
                // zh_xi = xi ^ n - 1
                let xi_n = self.get_xi_n(main_gate, region, offset)?;
                let zh_xi = main_gate.add_constant(region, &xi_n, -C::ScalarExt::one(), offset)?;
                self.evals.zh_xi = Some(zh_xi.clone());
                Ok(zh_xi)
            }
            Some(zh_xi) => Ok(zh_xi.clone()),
        }
    }

    fn get_l1_xi(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        match &self.evals.l1_xi {
            None => {
                let n = C::ScalarExt::from(self.n as u64);
                let one = C::ScalarExt::one();
                let zero = C::ScalarExt::zero();

                // l1_xi = w * (xi ^ n - 1) / (n * (xi - w))
                let n_xi_sub_w_value = self.xi.value.and_then(|xi| self.w.value.map(|w| (xi - w) * n));
                let (_, _, n_xi_sub_w, _, _) = main_gate.combine(
                    region,
                    [
                        Term::Assigned(self.xi, n),
                        Term::Assigned(self.w, -n),
                        Term::Unassigned(n_xi_sub_w_value, -one),
                        Term::Zero,
                        Term::Zero,
                    ],
                    zero,
                    offset,
                    CombinationOptionCommon::OneLinerAdd.into(),
                )?;

                let zh_xi = self.get_zh_xi(main_gate, region, offset)?;
                let w_zh_xi = main_gate.mul(region, self.w, &zh_xi, offset)?;
                let l1_xi = main_gate.div_unsafe(region, &w_zh_xi, &n_xi_sub_w, offset)?;

                Ok(l1_xi)
            }
            Some(l1_xi) => Ok(l1_xi.clone()),
        }
    }

    fn get_pi_xi(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        match &self.evals.pi_xi {
            None => {
                let n = C::ScalarExt::from(self.n as u64);
                let one = C::ScalarExt::one();
                let zero = C::ScalarExt::zero();

                let w_vec = self.pow_vec(main_gate, self.w, self.l, region, offset)?;

                let mut pi_vec = vec![];
                for i in 0..self.l {
                    let wi = &w_vec[i as usize];
                    // li_xi = (w ^ i) * (xi ^ n - 1) / (n * (xi - w ^ i))
                    let n_xi_sub_w_i_value = self.xi.value.and_then(|xi| self.w.value.map(|wi| (xi - wi) * n));
                    let (_, _, n_xi_sub_w, _, _) = main_gate.combine(
                        region,
                        [
                            Term::Assigned(self.xi, n),
                            Term::Assigned(wi, -n),
                            Term::Unassigned(n_xi_sub_w_i_value, -one),
                            Term::Zero,
                            Term::Zero,
                        ],
                        zero,
                        offset,
                        CombinationOptionCommon::OneLinerAdd.into(),
                    )?;

                    let zh_xi = self.get_zh_xi(main_gate, region, offset)?;
                    let wi_zh_xi = main_gate.mul(region, wi, &zh_xi, offset)?;
                    let li_xi = main_gate.div_unsafe(region, &wi_zh_xi, &n_xi_sub_w, offset)?;

                    pi_vec.push(li_xi);
                }

                let mut pi_xi = (&pi_vec)[0].clone();
                for i in 1..self.l {
                    pi_xi = main_gate.add(region, pi_xi, (&pi_vec)[i as usize].clone(), offset)?;
                }
                self.evals.pi_xi = Some(pi_xi.clone());
                Ok(pi_xi)
            }
            Some(l1_xi) => Ok(l1_xi.clone()),
        }
    }

    fn get_r0(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        /*
         * t1 = a_xi + beta * sigma1_xi + gamma;
         * t2 = b_xi + beta * sigma2_xi + gamma;
         * r0 = pi_xi - l1_xi * alpha ^ 2
         * - alpha * t1 * t2 * (c_xi + gamma) * z_xiw
         */

        let pi_xi = self.get_pi_xi(main_gate, region, offset)?;

        let l1_xi = self.get_l1_xi(main_gate, region, offset)?;
        let alpha2 = main_gate.mul2(region, self.alpha, offset)?;
        let l1_xi_alpha2 = main_gate.mul(region, l1_xi, alpha2, offset)?;

        let t1 = main_gate.mul(region, self.beta, self.evals.sigma1_xi, offset)?;
        let t1 = self.main_gate_add_array(main_gate, vec![self.evals.a_xi, &t1, self.gamma], region, offset)?;

        let t2 = main_gate.mul(region, self.beta, self.evals.sigma2_xi, offset)?;
        let t2 = self.main_gate_add_array(main_gate, vec![self.evals.b_xi, &t2, self.gamma], region, offset)?;

        let c_xi_gamma = main_gate.add(region, self.evals.c_xi, self.gamma, offset)?;
        let alpha_t1_t2_c_xi_gamma_z_xiw = self.main_gate_mul_array(
            main_gate,
            vec![&t1, &t2, self.alpha, &c_xi_gamma, self.evals.z_xiw],
            region,
            offset,
        )?;

        let r0 = main_gate.sub(region, pi_xi, l1_xi_alpha2, offset)?;
        let r0 = main_gate.sub(region, r0, alpha_t1_t2_c_xi_gamma_z_xiw, offset)?;

        Ok(r0)
    }

    fn main_gate_mul_array(
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        l: Vec<&AssignedValue<C::ScalarExt>>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        let mut base = l[0].clone();

        for i in 1..l.len() {
            base = main_gate.mul(region, base, l[i].clone(), offset)?;
        }

        Ok(base)
    }

    fn main_gate_add_array(
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        l: Vec<&AssignedValue<C::ScalarExt>>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        let mut base = l[0].clone();

        for i in 1..l.len() {
            base = main_gate.mul(region, base, l[i].clone(), offset)?;
        }

        Ok(base)
    }

    fn get_r (
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<SchemeItem<C>, Error> {
        let a = CommitQuery{c: Some(self.commits.a), v: Some(self.evals.a_xi)};
        let b = CommitQuery{c: Some(self.commits.b), v: Some(self.evals.b_xi)};
        let c = CommitQuery{c: Some(self.commits.c), v: Some(self.evals.c_xi)};
        let qm = CommitQuery{c: Some(self.params.q_m), v: None};
        let ql = CommitQuery{c: Some(self.params.q_l), v: None};
        let qr = CommitQuery{c: Some(self.params.q_r), v: None};
        let qo = CommitQuery{c: Some(self.params.q_o), v: None};
        let qc = CommitQuery{c: Some(self.params.q_c), v: None};
        let z = CommitQuery{c: Some(self.commits.z), v: None};
        let zxi = CommitQuery{c: Some(self.commits.z), v: None};
        let sigma1 = CommitQuery{c: None, v: Some(self.evals.sigma1_xi)};
        let sigma2 = CommitQuery{c: None, v: Some(self.evals.sigma2_xi)};
        let sigma3 = CommitQuery{c: Some(self.params.sigma3), v: None};
        let tl = CommitQuery{c: Some(self.commits.tl), v: None};
        let tm = CommitQuery{c: Some(self.commits.tm), v: None};
        let th = CommitQuery{c: Some(self.commits.th), v: None};
        let pi_xi = self.get_pi_xi(main_gate, region, offset)?;
        let l1_xi = self.get_l1_xi(main_gate, region, offset)?;
        let xi_n = self.get_xi_n(main_gate, region, offset)?;
        let xi_2n = self.get_xi_2n(main_gate, region, offset)?;
        let zh_xi = self.get_zh_xi(main_gate, region, offset)?;
        let neg_one = main_gate.neg_with_constant(region, self.one, C::ScalarExt::zero(), offset)?;
        Ok(eval!(a) * eval!(b) * commit!(qm) + eval!(a) * commit!(ql)
            + eval!(b) * commit!(qr) + eval!(c) * commit!(qo) + scalar!(pi_xi) + commit!(qc)
            + scalar!(self.alpha) * (
                  (eval!(a) + (scalar!(self.beta) * scalar!(self.xi)) + scalar!(self.gamma))
                * (eval!(b) + (scalar!(self.beta) * scalar!(self.xi)) + scalar!(self.gamma))
                * (eval!(c) + (scalar!(self.beta) * scalar!(self.xi)) + scalar!(self.gamma))
                * commit!(z)
                + (eval!(a) + (scalar!(self.beta) * eval!(sigma1)) + scalar!(self.gamma))
                * (eval!(b) + (scalar!(self.beta) * eval!(sigma2)) + scalar!(self.gamma))
                * (eval!(c) + (scalar!(self.beta) * commit!(sigma3)) + scalar!(self.gamma))
                * eval!(zxi)
              )
            + scalar!(self.alpha) * scalar!(self.alpha) * scalar!(l1_xi) * (commit!(z) + scalar!(neg_one))
            + scalar!(zh_xi) * (
                  commit!(tl)
                + scalar!(xi_n) * commit!(tm)
                + scalar!(xi_2n) * commit!(th)
            )
        )
    }

    /* This should be calculated from r1, r0 = get_r().eval()? */
    fn get_r1(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::ScalarExt>, Error> {
        /* t0 = a_xi * b_xi * q_m + a * q_l + b * q_r + c * q_o + q_c
         * t1 = a_xi + beta * xi + gamma;
         * t2 = b_xi + beta * k1 * xi + gamma;
         * t3 = c_xi + beta * k2 * xi + gamma;
         * t4 = a_xi + beta * sigma1_xi + gamma;
         * t5 = b_xi + beta * sigma2_xi + gamma;
         * r1 = t0
         *      + (t1 * t2 * t3 * alpha + l1_xi * alpha^2) * z
         *      - t4 * t5 * alpha * beta * z_xiw * sigma3
         *      + zh_xi * (tl + xi^n * tm + xi^2n * th)
         */
        let t0 = {
            let r = main_gate.mul(region, self.evals.a_xi, self.evals.b_xi, offset)?;
            let o1 = ecc_gate.mul_var(region, self.params.q_m, &r, offset)?;
            let o2 = ecc_gate.mul_var(region, self.params.q_l, self.evals.a_xi, offset)?;
            let o3 = ecc_gate.mul_var(region, self.params.q_r, self.evals.b_xi, offset)?;
            let o4 = ecc_gate.mul_var(region, self.params.q_o, self.evals.c_xi, offset)?;
            let o5 = ecc_gate.add(region, &o1, &o2, offset)?;
            let o6 = ecc_gate.add(region, &o3, &o4, offset)?;
            let o7 = ecc_gate.add(region, &o5, &o6, offset)?;
            let o8 = ecc_gate.add(region, &o7, self.params.q_c, offset)?;
            o8
        };
        let t1 = {
            let r = main_gate.mul(region, self.beta, self.xi, offset)?;
            let r = self.main_gate_add_array(main_gate, vec![&r, self.evals.a_xi, self.gamma], region, offset)?;
            r
        };
        let t2 = {
            let r = self.main_gate_mul_array(main_gate, vec![self.beta, self.xi, self.k1], region, offset)?;
            let r = self.main_gate_add_array(main_gate, vec![&r, self.evals.b_xi, self.gamma], region, offset)?;
            r
        };
        let t3 = {
            let r = self.main_gate_mul_array(main_gate, vec![self.beta, self.xi, self.k2], region, offset)?;
            let r = self.main_gate_add_array(main_gate, vec![&r, self.evals.c_xi, self.gamma], region, offset)?;
            r
        };
        let t4 = {
            let r = main_gate.mul(region, self.beta, self.evals.sigma1_xi, offset)?;
            let r = self.main_gate_add_array(main_gate, vec![&r, self.evals.a_xi, self.gamma], region, offset)?;
            r
        };
        let t5 = {
            let r = main_gate.mul(region, self.beta, self.evals.sigma2_xi, offset)?;
            let r = self.main_gate_add_array(main_gate, vec![&r, self.evals.b_xi, self.gamma], region, offset)?;
            r
        };

        // t0 + (t1 * t2 * t3 * alpha + l1_xi * alpha^2) * z
        let l1_xi = self.get_l1_xi(main_gate, region, offset)?;
        let r = {
            let x = self.main_gate_mul_array(main_gate, vec![&t1, &t2, &t3, self.alpha], region, offset)?;
            let y = self.main_gate_mul_array(main_gate, vec![&l1_xi, self.alpha, self.alpha], region, offset)?;
            main_gate.add(region, x, y, offset)?
        };
        let r = ecc_gate.mul_var(region, self.commits.z, &r, offset)?;
        let r = ecc_gate.add(region, &t0, &r, offset)?;

        // - t4 * t5 * alpha * beta * z_xiw * sigma3
        let t4_t5_alpha_beta_z_xiw = self.main_gate_mul_array(main_gate, vec![&t4, &t5, self.alpha, self.beta, self.evals.z_xiw], region, offset)?;
        let neg_t4_t5_alpha_beta_z_xiw = main_gate.neg_with_constant(region, t4_t5_alpha_beta_z_xiw, C::ScalarExt::zero(), offset)?;
        let neg_t4_t5_alpha_beta_z_xiw_sigma3 = ecc_gate.mul_var(region, self.params.sigma3, &neg_t4_t5_alpha_beta_z_xiw, offset)?;
        let r = ecc_gate.add(region, &r, &neg_t4_t5_alpha_beta_z_xiw_sigma3, offset)?;

        // - zh_xi * (tl + xi^n * tm + xi^2n * th)
        let xi_n = self.get_xi_n(main_gate, region, offset)?;
        let xi_2n = self.get_xi_2n(main_gate, region, offset)?;
        let zh_xi = self.get_zh_xi(main_gate, region, offset)?;
        let neg_zh_xi = main_gate.neg_with_constant(region, zh_xi, C::ScalarExt::zero(), offset)?;
        let xi_n_tm = ecc_gate.mul_var(region, self.commits.tm, &xi_n, offset)?;
        let xi_2n_th = ecc_gate.mul_var(region, self.commits.th, &xi_2n, offset)?;
        let s = ecc_gate.add(region, self.commits.tl, &xi_n_tm, offset)?;
        let s = ecc_gate.add(region, &s, &xi_2n_th, offset)?;
        let neg_zh_sum = ecc_gate.mul_var(region, &s, &neg_zh_xi, offset)?;
        let r = ecc_gate.add(region, &r, &neg_zh_sum, offset)?;
        Ok(r)
    }

    fn get_e1(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        let r0_xi = self.get_r0(main_gate, region, offset)?;
        let v0 = SPE(
            [
                self.evals.sigma2_xi,
                self.evals.sigma1_xi,
                self.evals.c_xi,
                self.evals.b_xi,
                self.evals.a_xi,
                &r0_xi,
            ]
            .to_vec(),
            self.v,
        );
        let v1 = SPE([self.evals.z_xiw].to_vec(), self.one);
        MPE([&v0 as &dyn EvalAggregator<C>, &v1].to_vec(), self.u).aggregate(main_gate, region, self.one, offset)
    }

    fn get_f1(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::ScalarExt>, Error> {
        let r1 = self.get_r1(main_gate, ecc_gate, region, offset)?;
        let v0 = SPC(
            [self.params.sigma2, self.params.sigma1, self.commits.c, self.commits.b, self.commits.a, &r1].to_vec(),
            self.v,
        );
        let v1 = SPC([self.commits.z].to_vec(), self.one);
        MPC([&v0 as &dyn MSMAggregator<C>, &v1].to_vec(), self.u).aggregate(ecc_gate, region, self.one, offset)
    }

    fn get_wx(
        &mut self,
        main_gate: &MainGate<C::ScalarExt>,
        ecc_gate: &BaseFieldEccChip<C>,
        ws: Vec<SingleOpeningProof<C>>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<MultiOpeningProof<C>, Error> {
        let e1 = self.get_e1(main_gate, region, offset)?;
        let f1 = self.get_f1(main_gate, ecc_gate, region, offset)?;
        let mut wxs = Vec::new();
        ws.iter().for_each(|w| {
            wxs.push(w.w.clone());
        });
        let wxs = SPC(wxs.iter().collect(), self.u).aggregate(ecc_gate, region, self.one, offset)?;
        Ok(MultiOpeningProof{w_x: wxs.clone(), w_g: wxs, e: e1, f :f1})

    }
}
