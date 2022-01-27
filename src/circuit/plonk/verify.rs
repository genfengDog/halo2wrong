use super::super::multiopen::{MSMAggregator, EvalAggregator, MPC, SPC, SPE, MPE};
use crate::WrongExt;
use halo2::circuit::Region;
use halo2::arithmetic::{CurveAffine, FieldExt};
use halo2arith::main_gate::five::main_gate::{
    MainGate,
    CombinationOption,
};
use halo2arith::main_gate::five::range::RangeConfig;
use halo2::plonk::Error;
use halo2arith::{
    halo2, AssignedCondition, AssignedValue, MainGateInstructions,
    CombinationOptionCommon, Term
};
use crate::circuit::ecc::{AssignedPoint, Point};
use crate::circuit::ecc::base_field_ecc::{BaseFieldEccInstruction, BaseFieldEccChip};

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
    wz: &'a AssignedPoint<N>,
}

pub struct VerifyEvals<'a, N: FieldExt> {
    a_xi: &'a AssignedValue<N>,
    b_xi: &'a AssignedValue<N>,
    c_xi: &'a AssignedValue<N>,
    sigma1_xi: &'a AssignedValue<N>,
    sigma2_xi: &'a AssignedValue<N>,
    z_xiw: &'a AssignedValue<N>,
    zh_xi: &'a AssignedValue<N>,
    l1_xi: &'a AssignedValue<N>,
    pi_xi: &'a AssignedValue<N>,
}

pub struct PlonkVerifierParams<'a, C: CurveAffine> {
    params: ParamsPreprocessed<'a, C::ScalarExt>,
    commits: VerifyCommitments<'a, C::ScalarExt>,
    evals: VerifyEvals<'a, C::ScalarExt>,
    one: &'a AssignedValue<C::ScalarExt>,
    beta: &'a AssignedValue<C::ScalarExt>,
    gamma: &'a AssignedValue<C::ScalarExt>,
    alpha: &'a AssignedValue<C::ScalarExt>,
    xi: &'a AssignedValue<C::ScalarExt>,
    u: &'a AssignedValue<C::ScalarExt>,
    v: &'a AssignedValue<C::ScalarExt>,
    k1: &'a AssignedValue<C::ScalarExt>,
    k2: &'a AssignedValue<C::ScalarExt>,
    w: &'a AssignedValue<C::ScalarExt>, //TODO the unit root of 2^n = 1
}

impl<C: CurveAffine> PlonkVerifierParams<'_, C> {
    fn get_r0 (
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> AssignedValue<C::ScalarExt> {
        /*
         * t1 = a_xi + beta * sigma1_xi + gamma;
         * t2 = b_xi + beta * sigma2_xi + gamma;
         * r0 = pi_xi - l1_xi * alpha ^ 2
         * - alpha * t1 * t2 * (c_xi + gamma) * z_xiw
         */
        self.v.clone()
    }
    fn get_r1 (
        &self,
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
         * t0 + (t1*t2*t3*alpha + l1_xi * alpha^2) z + zh_xi(tl + xi^n tm + xi^2n th)
         */
        let t0 = {
            let r = main_gate.mul(region, self.evals.a_xi, self.evals.b_xi, offset)?;
            let o1 = ecc_gate.mul_var(region, self.params.q_m, &r, offset)?;
            let o2 = ecc_gate.mul_var(region, self.params.q_l, self.evals.a_xi, offset)?;
            let o3 = ecc_gate.mul_var(region, self.params.q_r, self.evals.b_xi, offset)?;
            let o4 = ecc_gate.mul_var(region, self.params.q_o, self.evals.c_xi, offset)?;
            let o5 = ecc_gate.add(region, &o1, &o2, offset)?;
            let o6 = ecc_gate.add(region, &o5, &o3, offset)?;
            let o7 = ecc_gate.add(region, &o6, &o5, offset)?;
            let o8 = ecc_gate.add(region, &o7, self.params.q_c, offset)?;
            o8
        };
        let t1 = {
            let r = main_gate.mul(region, self.beta, self.xi, offset)?;
            let r = main_gate.add(region, &r, self.evals.a_xi, offset)?;
            let r = main_gate.mul(region, &r, self.gamma, offset)?;
            r
        };
        let t2 = {
            let r = main_gate.mul(region, self.beta, self.xi, offset)?;
            let r = main_gate.mul(region, &r, self.k1, offset)?;
            let r = main_gate.add(region, &r, self.evals.b_xi, offset)?;
            let r = main_gate.mul(region, &r, self.gamma, offset)?;
            r
        };
        let t3 = {
            let r = main_gate.mul(region, self.beta, self.xi, offset)?;
            let r = main_gate.mul(region, &r, self.k2, offset)?;
            let r = main_gate.add(region, &r, self.evals.c_xi, offset)?;
            let r = main_gate.mul(region, &r, self.gamma, offset)?;
            r
        };
        let t4 = {
            let r = main_gate.mul(region, self.beta, self.evals.sigma1_xi, offset)?;
            let r = main_gate.add(region, &r, self.evals.a_xi, offset)?;
            let r = main_gate.mul(region, &r, self.gamma, offset)?;
            r
        };
        let t5 = {
            let r = main_gate.mul(region, self.beta, self.evals.sigma2_xi, offset)?;
            let r = main_gate.add(region, &r, self.evals.b_xi, offset)?;
            let r = main_gate.mul(region, &r, self.gamma, offset)?;
            r
        };
        // t0 + (t1*t2*t3*alpha + l1_xi * alpha^2) z + zh_xi(tl + xi^n tm + xi^2n th)
        let r = {
            let x = main_gate.mul(region, &t1, &t2, offset)?;
            let x = main_gate.mul(region, &x, &t3, offset)?;
            let x = main_gate.mul(region, &x, self.alpha, offset)?;
            let y = main_gate.mul(region, self.alpha, self.alpha, offset)?;
            let y = main_gate.mul(region, &y, self.evals.l1_xi, offset)?;
            main_gate.add(region, x, y, offset)?
        };
        let r = ecc_gate.mul_var(region, self.commits.z, &r, offset)?;
        let r = ecc_gate.add(region, &t0, &r, offset)?;
        // TODO, need xi^n
        Ok(r)
    }
    fn get_e1 (
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        let r0_xi = self.get_r0(main_gate, ecc_gate, region, offset);
        let v0 = SPE([
            self.evals.sigma2_xi,
            self.evals.sigma1_xi,
            self.evals.c_xi,
            self.evals.b_xi,
            self.evals.a_xi,
            &r0_xi
        ].to_vec(), self.v);
        let v1 = SPE([self.evals.z_xiw].to_vec(), self.one);
        MPE([&v0 as &dyn EvalAggregator<C>, &v1].to_vec(), self.u).aggregate(main_gate, region, self.one, offset)
    }
    fn get_f1 (
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::ScalarExt>, Error>{
        let r0 = self.get_r1(main_gate, ecc_gate, region, offset)?;
        let v0 = SPC([
            self.params.sigma2,
            self.params.sigma1,
            self.commits.c,
            self.commits.b,
            self.commits.a,
            &r0,
        ].to_vec(), self.v);
        let v1 = SPC([self.commits.z].to_vec(), self.one);
        MPC([&v0 as &dyn MSMAggregator<C>, &v1].to_vec(), self.u).aggregate(ecc_gate, region, self.one, offset)
    }
/*
    fn get_wz (
    )
    fn get_wz
*/
}

