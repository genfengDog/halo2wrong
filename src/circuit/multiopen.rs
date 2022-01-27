use crate::WrongExt;
use halo2::circuit::Region;
use halo2::arithmetic::{CurveAffine, Field, FieldExt};
use halo2arith::main_gate::five::main_gate::{
    MainGate,
    CombinationOption,
};
use halo2::plonk::Error;
use halo2arith::{
    halo2, AssignedValue, MainGateInstructions,
    CombinationOptionCommon, Term
};
use crate::circuit::ecc::{AssignedPoint};
use crate::circuit::ecc::base_field_ecc::{BaseFieldEccInstruction, BaseFieldEccChip};

trait Commitment<C: CurveAffine> {
   fn append_term (
        &self,
        ecc_gate: &impl BaseFieldEccInstruction<C>,
        region: &mut Region<'_, C::ScalarExt>,
        commitment: &AssignedPoint<C::ScalarExt>,
        scalar: &AssignedValue<C::ScalarExt>,
        offset: &mut usize
    ) -> Result<Self, Error> where Self: Sized;

    fn factor (
        &self,
        ecc_gate: &impl BaseFieldEccInstruction<C>,
        region: &mut Region<'_, C::ScalarExt>,
        factor: &AssignedValue<C::ScalarExt>,
        offset: &mut usize
    ) -> Result<Self, Error> where Self: Sized;
}

impl<C: CurveAffine> Commitment<C> for AssignedPoint<C::ScalarExt> {
   fn append_term (
        &self,
        ecc_gate: &impl BaseFieldEccInstruction<C>,
        region: &mut Region<'_, C::ScalarExt>,
        commitment: &AssignedPoint<C::ScalarExt>,
        scalar: &AssignedValue<C::ScalarExt>,
        offset: &mut usize
    ) -> Result<Self, Error> where Self: Sized {
        let m = ecc_gate.mul_var(region, &commitment, &scalar, offset)?;
        ecc_gate.add(region, self, &m, offset)
    }
    fn factor (
        &self,
        ecc_gate: &impl BaseFieldEccInstruction<C>,
        region: &mut Region<'_, C::ScalarExt>,
        factor: &AssignedValue<C::ScalarExt>,
        offset: &mut usize
    ) -> Result<Self, Error> where Self: Sized {
        ecc_gate.mul_var(region, self, factor, offset)
    }
}

trait Eval<N: FieldExt> {
   fn append_term (
        &self,
        main_gate: &MainGate<N>,
        region: &mut Region<'_, N>,
        eval: &AssignedValue<N>,
        scalar: &AssignedValue<N>,
        offset: &mut usize
    ) -> Result<Self, Error> where Self: Sized;
    fn factor (
        &self,
        main_gate: &MainGate<N>,
        region: &mut Region<'_, N>,
        factor: &AssignedValue<N>,
        offset: &mut usize
    ) -> Result<AssignedValue<N>, Error>;
}

impl<N: FieldExt> Eval<N> for AssignedValue<N> {
   fn append_term (
        &self,
        main_gate: &MainGate<N>,
        region: &mut Region<'_, N>,
        eval: &AssignedValue<N>,
        scalar: &AssignedValue<N>,
        offset: &mut usize
    ) -> Result<Self, Error> where Self: Sized {
        //a * b + d - sd_next*d_next = 0
        let (_, _, _, _, e_next) = main_gate.combine(
            region,
            [
                Term::Assigned(eval, N::zero()),
                Term::Assigned(scalar, N::zero()),
                Term::Zero,
                Term::Zero,
                Term::Assigned(self, N::zero()),
            ],
            N::zero(),
            offset,
            CombinationOption::Common(CombinationOptionCommon::CombineToNextMul(N::one()))
        )?;
        Ok(e_next)
    }
    fn factor (
        &self,
        main_gate: &MainGate<N>,
        region: &mut Region<'_, N>,
        factor: &AssignedValue<N>,
        offset: &mut usize
    ) -> Result<AssignedValue<N>, Error> {
        main_gate.mul(region, self, factor, offset)
    }
}

pub trait EvalAggregator <C: CurveAffine> {
    fn aggregate (
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        one: &AssignedValue<C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error>;
}

pub struct SPE <'a, C: CurveAffine> (
    pub Vec<&'a AssignedValue<C::ScalarExt>>,
    pub &'a AssignedValue<C::ScalarExt>
);

pub struct MPE <'a, C: CurveAffine> (
    pub Vec<&'a dyn EvalAggregator <C>>,
    pub &'a AssignedValue<C::ScalarExt>
);

/* The multiExp with identity scalar */
/* TODO: add common wnaf optimization here */
impl<C: CurveAffine> EvalAggregator <C> for SPE<'_, C> {
    fn aggregate(
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        one: &AssignedValue<C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        let SPE (comms, v) = self;
        let r = if let Some ((fst, tail)) = comms.split_first() {
            let mut eva = (*fst).clone();
            tail.iter().for_each(|val| {
                let acc = eva.factor(main_gate, region, &v, offset).unwrap();
                eva = acc.append_term(main_gate, region, val, one, offset).unwrap()
            });
            Ok(eva.clone())
        } else {
            Err(Error::Synthesis)
        };
        r
    }
}

impl<C: CurveAffine> EvalAggregator<C> for MPE<'_, C> {
    fn aggregate(
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        one: &AssignedValue<C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        let MPE (comms, v) = self;
        let r = if let Some ((fst, tail)) = comms.split_first() {
            let mut eva = fst.aggregate(main_gate, region, one, offset)?;
            tail.iter().for_each(|val| {
                let acc = eva.factor(main_gate, region, &v, offset).unwrap();
                let val = val.aggregate(main_gate, region, one, offset).unwrap();
                eva = acc.append_term(main_gate, region, &val, one, offset).unwrap()
            });
            Ok(eva.clone())
        } else {
            Err(Error::Synthesis)
        };
        r
    }
}

pub trait MSMAggregator <C: CurveAffine> {
    fn aggregate (
        &self,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        one: &AssignedValue<C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::ScalarExt>, Error>;
}

pub struct SPC <'a, C: CurveAffine> (
    pub Vec<&'a AssignedPoint<C::ScalarExt>>,
    pub &'a AssignedValue<C::ScalarExt>
);

pub struct MPC <'a, C: CurveAffine> (
    pub Vec<&'a dyn MSMAggregator <C>>,
    pub &'a AssignedValue<C::ScalarExt>
);

/* The multiExp with identity scalar */
/* TODO: add common wnaf optimization here */
impl<C: CurveAffine> MSMAggregator <C> for SPC<'_, C> {
    fn aggregate(
        &self,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        one: &AssignedValue<C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::ScalarExt>, Error> {
        let SPC (comms, v) = self;
        let r = if let Some ((fst, tail)) = comms.split_first() {
            let mut eva = (*fst).clone();
            tail.iter().for_each(|val| {
                let acc = eva.factor(ecc_gate, region, &v, offset).unwrap();
                eva = acc.append_term(ecc_gate, region, val, one, offset).unwrap()
            });
            Ok(eva.clone())
        } else {
            Err(Error::Synthesis)
        };
        r
    }
}

impl<C: CurveAffine> MSMAggregator<C> for MPC<'_, C> {
    fn aggregate(
        &self,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        one: &AssignedValue<C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::ScalarExt>, Error> {
        let MPC (comms, v) = self;
        let r = if let Some ((fst, tail)) = comms.split_first() {
            let mut eva = fst.aggregate(ecc_gate, region, one, offset)?;
            tail.iter().for_each(|val| {
                let acc = eva.factor(ecc_gate, region, &v, offset).unwrap();
                let val = val.aggregate(ecc_gate, region, one, offset).unwrap();
                eva = acc.append_term(ecc_gate, region, &val, one, offset).unwrap()
            });
            Ok(eva.clone())
        } else {
            Err(Error::Synthesis)
        };
        r
    }
}

pub struct SinglePointCommitment<C: CurveAffine> {
    w: AssignedPoint<C::ScalarExt>,
    z: AssignedValue<C::ScalarExt>,
    f: AssignedPoint<C::ScalarExt>,
    eval: AssignedValue<C::ScalarExt>,
}

// (g^e + w_g, [1]) and (w_x, [x])
pub struct MultiOpeningProof<C: CurveAffine> {
    w_x: AssignedPoint<C::ScalarExt>,
    w_g: AssignedPoint<C::ScalarExt>,
    e: AssignedValue<C::ScalarExt>,
}
