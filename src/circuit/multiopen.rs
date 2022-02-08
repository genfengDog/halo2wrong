use crate::WrongExt;
use halo2::circuit::Region;
use halo2::arithmetic::{CurveAffine, FieldExt};
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

trait ArrayOps<N: FieldExt, T> {
    fn mul_array(
        &self,
        l: Vec<&T>,
        region: &mut Region<'_, N>,
        offset: &mut usize,
    ) -> Result<T, Error>;
    fn add_array(
        &self,
        l: Vec<&T>,
        region: &mut Region<'_, N>,
        offset: &mut usize,
    ) -> Result<T, Error>;
}

impl<N:FieldExt> ArrayOps<N, AssignedValue<N>> for MainGate<N> {
    fn mul_array(
        &self,
        l: Vec<&AssignedValue<N>>,
        region: &mut Region<'_, N>,
        offset: &mut usize,
    ) -> Result<AssignedValue<N>, Error> {
        let mut base = l[0].clone();
        for i in 1..l.len() {
            base = self.mul(region, base, l[i].clone(), offset)?;
        }
        Ok(base)
    }
    fn add_array(
        &self,
        l: Vec<&AssignedValue<N>>,
        region: &mut Region<'_, N>,
        offset: &mut usize,
    ) -> Result<AssignedValue<N>, Error> {
        let mut base = l[0].clone();
        for i in 1..l.len() {
            base = self.add(region, base, l[i].clone(), offset)?;
        }
        Ok(base)
    }
}

impl<C:CurveAffine> ArrayOps<C::ScalarExt, AssignedPoint<C::ScalarExt>> for BaseFieldEccChip<C> {
    fn mul_array(
        &self,
        _l: Vec<&AssignedPoint<C::ScalarExt>>,
        _region: &mut Region<'_, C::ScalarExt>,
        _offset: &mut usize,
    ) -> Result<AssignedPoint<C::ScalarExt>, Error> {
        Err(Error::Synthesis)
    }
    fn add_array(
        &self,
        l: Vec<&AssignedPoint<C::ScalarExt>>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::ScalarExt>, Error> {
        let mut base = l[0].clone();
        for i in 1..l.len() {
            base = self.add(region, &base, &l[i].clone(), offset)?;
        }
        Ok(base)
    }
}

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
        let v = eval.value.and_then(|eval_v| {
            scalar.value.and_then(|scalar_v| {
                self.value.and_then(|self_v| {
                    Some(eval_v * scalar_v + self_v)
                })
            })
        });
        let (_, _, _, res, _) = main_gate.combine(
            region,
            [
                Term::Assigned(eval, N::zero()),
                Term::Assigned(scalar, N::zero()),
                Term::Assigned(self, N::one()),
                Term::Unassigned(v, -N::one()),
                Term::Zero,
            ],
            N::zero(),
            offset,
            CombinationOption::Common(CombinationOptionCommon::OneLinerMul)
        )?;
        Ok(res)
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
            Ok(eva)
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

#[derive(Clone, Debug)]
pub struct CommitQuery<'a, C: CurveAffine> {
    pub c: Option<&'a AssignedPoint<C::ScalarExt>>,
    pub v: Option<&'a AssignedValue<C::ScalarExt>>,
}

/*
pub enum SchemeItem<'a, C: CurveAffine> {
    Poly((CommitQuery<'a, C>, bool)),
    Scalar(AssignedValue<C::ScalarExt>),
    Add(Vec<SchemeItem<'a, C>>),
    Mul(Vec<SchemeItem<'a, C>>),
}

impl<C: CurveAffine> std::ops::Add for SchemeItem<'_, C> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        match self {
            SchemeItem::<C>::Add(mut ls) => {
                ls.push(other);
                SchemeItem::Add(ls)
            },
            _ => SchemeItem::<C>::Add(vec![self, other]),
        }
    }
}

impl<C: CurveAffine> std::ops::Mul for SchemeItem<'_, C> {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        match self {
            SchemeItem::<C>::Mul(mut ls) => {
                ls.push(other);
                SchemeItem::Mul(ls)
            },
            _ => SchemeItem::<C>::Mul(vec![self, other]),
        }
    }
}

impl<C: CurveAffine> SchemeItem<'_, C> {
    fn eval(
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<(Option<AssignedPoint<C::ScalarExt>>, Option<AssignedValue<C::ScalarExt>>), Error> {
        match self {
            SchemeItem::Poly((cq, true)) => {
                Ok((cq.c.map(|c| c.clone()), None))
            },
            SchemeItem::Poly((cq, false)) => {
                Ok((None, cq.v.map(|c| c.clone())))
            },

            SchemeItem::Scalar(s) => {
                Ok((None, Some (s.clone())))
            },
            SchemeItem::Add(ls) => {
                let mut cs = Vec::new();
                let mut vs = Vec::new();
                ls.iter().for_each(|val| {
                    let (c, v) = val.eval(main_gate, ecc_gate, region, offset).unwrap();
                    c.map(|c| cs.push(c));
                    v.map(|v| vs.push(v));
                });
                let vs = vs.iter().collect::<Vec<_>>();
                let v = match vs[..] {
                    [] => None,
                    _ => Some (main_gate.add_array(vs, region, offset)?)
                };
                let cs = cs.iter().collect::<Vec<_>>();
                let c = match cs[..] {
                    [] => None,
                    _ => Some (ecc_gate.add_array(cs, region, offset)?)
                };
                Ok((c, v))
            }
            SchemeItem::Mul(ls) => {
                let mut cs = Vec::new();
                let mut vs = Vec::new();
                ls.iter().for_each(|val| {
                    let (c, v) = val.eval(main_gate, ecc_gate, region, offset).unwrap();
                    c.map(|c| cs.push(c));
                    v.map(|v| vs.push(v));
                });
                let vs = vs.iter().collect::<Vec<_>>();
                let v = match vs[..] {
                    [] => None,
                    _ => Some (main_gate.mul_array(vs, region, offset)?)
                };
                let cs = cs.iter().collect::<Vec<_>>();
                match cs[..] {
                    [] => Ok((None, v)),
                    [c] => {
                        match v {
                            None => Ok((Some(c.clone()), None)),
                            Some(v) => Ok((Some(ecc_gate.mul_var(region, c, &v, offset)?), None))
                        }
                    },
                    _ => Err(Error::Synthesis)
                }
            }
        }
    }
}

#[macro_export]
macro_rules! commit {
    ($x:expr) => {
        SchemeItem::<C>::Poly(($x.clone(), true))
    };
}
#[macro_export]
macro_rules! eval {
    ($x:expr) => {
        SchemeItem::<C>::Poly(($x.clone(), false))
    };
}
#[macro_export]
macro_rules! scalar {
    ($x:expr) => {
        SchemeItem::<C>::Scalar($x.clone())
    };
}
*/

pub struct SingleOpeningProof<C: CurveAffine> {
    pub w: AssignedPoint<C::ScalarExt>,
    pub z: AssignedValue<C::ScalarExt>,
    pub f: AssignedPoint<C::ScalarExt>,
    pub eval: AssignedValue<C::ScalarExt>,
}

// (g^e + w_g, [1]) and (w_x, [x])
pub struct MultiOpeningProof<C: CurveAffine> {
    pub w_x: AssignedPoint<C::ScalarExt>,
    pub w_g: AssignedPoint<C::ScalarExt>,
    pub f: AssignedPoint<C::ScalarExt>,
    pub e: AssignedValue<C::ScalarExt>,
}

/****** new schema ******/
#[derive(Clone, Debug)]
pub enum ScalarItem<'a, C: CurveAffine> {
    Unit(AssignedValue<C::ScalarExt>),
    Eval(CommitQuery<'a, C>),
    Add(Vec<ScalarItem<'a, C>>),
    Mul(Vec<ScalarItem<'a, C>>)
}


impl<C: CurveAffine> ScalarItem<'_, C> {
    fn eval(
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedValue<C::ScalarExt>, Error> {
        match self {
            ScalarItem::Unit(v) => Ok(v.clone()),
            ScalarItem::Eval(cq) => Ok(cq.v.unwrap().clone()),
            ScalarItem::Add(ls) => {
                let ls_res: Result<Vec<_>, _> = ls.iter().map(|e| e.eval(main_gate, region, offset)).collect();
                let ls = ls_res?;
                main_gate.add_array(ls.iter().collect(), region, offset)
            },
            ScalarItem::Mul(ls) => {
                let ls_res: Result<Vec<_>, _> = ls.iter().map(|e| e.eval(main_gate, region, offset)).collect();
                let ls = ls_res?;
                main_gate.mul_array(ls.iter().collect(), region, offset)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum PointItem<'a, C: CurveAffine> {
    Commit(CommitQuery<'a, C>, Option<ScalarItem<'a, C>>),
    Add(Vec<PointItem<'a, C>>)
}

impl<C: CurveAffine> PointItem<'_, C> {
    pub fn eval(
        &self,
        main_gate: &MainGate<C::ScalarExt>,
        ecc_gate: &BaseFieldEccChip<C>,
        region: &mut Region<'_, C::ScalarExt>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::ScalarExt>, Error> {
        match self {
            PointItem::Commit(cq, scalar) => {
                match scalar {
                    Some(scalar) => {
                        let scalar = scalar.eval(main_gate, region, offset)?;
                        ecc_gate.mul_var(region, cq.c.unwrap(), &scalar, offset)
                    },
                    None => {
                        Ok(cq.c.unwrap().clone())
                    }
                }
            },
            PointItem::Add(ls) => {
                let ls: Result<Vec<_>, _> = ls.iter().map(|x| x.eval(main_gate, ecc_gate, region, offset)).collect();
                let ls = ls?;
                ecc_gate.add_array(ls.iter().collect(), region, offset)
            },
        }
    }
}

impl<C: CurveAffine> std::ops::Add for ScalarItem<'_, C> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        match self {
            ScalarItem::<C>::Add(mut scalars) => {
                scalars.push(other);
                ScalarItem::Add(scalars)
            },
            _ => ScalarItem::<C>::Add(vec![self, other]),
        }
    }
}

impl<C: CurveAffine> std::ops::Mul for ScalarItem<'_, C> {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        match self {
            ScalarItem::<C>::Mul(mut scalars) => {
                scalars.push(other);
                ScalarItem::Mul(scalars)
            },
            _ => ScalarItem::<C>::Mul(vec![self, other]),
        }
    }
}

impl<C: CurveAffine> std::ops::Add for PointItem<'_, C> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        match self {
            PointItem::<C>::Add(mut points) => {
                points.push(other);
                PointItem::Add(points)
            },
            _ => PointItem::<C>::Add(vec![self, other]),
        }
    }
}

impl<'a, C: CurveAffine> std::ops::Mul<ScalarItem<'a, C>> for PointItem<'a, C> {
    type Output = Self;
    fn mul(self, other: ScalarItem::<'a, C>) -> Self {
        match self {
            PointItem::<C>::Commit(base, scalar) => {
                let new_scalar = match scalar {
                    Some(scalar) => Some(scalar * other),
                    _ => Some(other)
                };
                PointItem::Commit(base, new_scalar)
            },
            PointItem::<C>::Add(points) => {
                let new_points = points.into_iter().map(|x| { x * other.clone() }).collect();
                PointItem::<C>::Add(new_points)
            }
        }
    }
}

impl<'a, C: CurveAffine> std::ops::Mul<PointItem<'a, C>> for ScalarItem<'a, C> {
    type Output = PointItem<'a, C>;
    fn mul(self, other: PointItem::<'a, C>) -> PointItem<'a, C> {
        other * self
    }
}

#[macro_export]
macro_rules! commit {
    ($x:expr) => {
        crate::circuit::multiopen::PointItem::<C>::Commit($x.clone(), None)
    };
}

#[macro_export]
macro_rules! eval {
    ($x:expr) => {
        crate::circuit::multiopen::ScalarItem::<C>::Eval($x.clone())
    };
}

#[macro_export]
macro_rules! scalar {
    ($x:expr) => {
        crate::circuit::multiopen::ScalarItem::<C>::Unit($x.clone())
    };
}