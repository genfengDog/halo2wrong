use crate::rns::Integer;
use crate::circuit::main_gate::{MainGateConfig};

use super::{AssignedCondition, AssignedInteger};
use super::main_gate::{MainGate, MainGateInstructions};
use super::integer::{IntegerConfig, IntegerChip, IntegerInstructions};
use halo2::arithmetic::{FieldExt, CurveAffine};
use halo2::circuit::{Region, Layouter};
use halo2::plonk::Error;
use std::marker::PhantomData;
use crate::NUMBER_OF_LIMBS;

mod add;

/* Emulate CurveAffine point undert field F */
#[derive(Default, Clone, Debug)]
pub struct Point<C: CurveAffine, F: FieldExt> {
    x: Integer<F>,
    y: Integer<F>,
    _marker: PhantomData<C::Base>
}

impl<C: CurveAffine, F: FieldExt> Point<C, F> {
    fn new(x: Integer<F>, y: Integer<F>) -> Self {
        Point { x, y, _marker:PhantomData }
    }
}

pub struct AssignedPoint<C: CurveAffine, F: FieldExt > {
    x: AssignedInteger<F>,
    y: AssignedInteger<F>,
    // indicate whether the poinit is the identity point of curve or not
    z: AssignedCondition<F>,
    _marker: PhantomData<C::Base>
}

impl<C: CurveAffine, F: FieldExt> AssignedPoint<C, F> {
    pub fn new(
        x:AssignedInteger<F>,
        y:AssignedInteger<F>,
        z:AssignedCondition<F>
    ) -> AssignedPoint<C,F> {
        AssignedPoint{ x, y, z, _marker:PhantomData }
    }
    pub fn is_identity(&self) -> AssignedCondition<F> {
        self.z.clone()
    }
}

/// Linear combination term
pub enum Term<C: CurveAffine, F: FieldExt> {
    Assigned(AssignedPoint<C, F>, F),
    Unassigned(Option<Point<C, F>>, F),
}

#[derive(Clone, Debug)]
pub struct EccConfig {
    integer_chip_config: IntegerConfig,
    main_gate_config: MainGateConfig,
}

// we need template arg C to extract curve constants including a and b
pub struct EccChip<C: CurveAffine, F: FieldExt> {
    config: EccConfig,
    integer_chip: IntegerChip<C::Base, F>,
    // We need to assign following integers based on constants of curve C
    a: AssignedInteger<F>,
    b: AssignedInteger<F>,
}


impl<C: CurveAffine, F: FieldExt> EccChip<C, F> {
    fn new(
        layouter: &mut impl Layouter<F>,
        config: EccConfig,
        integer_chip: IntegerChip<C::Base, F>
    ) -> Result<Self, Error> {
        let ca = Integer::<F>::from_bytes_le(
                &C::a().to_bytes(),
                NUMBER_OF_LIMBS,
                integer_chip.rns.bit_len_limb
        );
        let cb = Integer::<F>::from_bytes_le(
                &C::b().to_bytes(),
                NUMBER_OF_LIMBS,
                integer_chip.rns.bit_len_limb
        );

        let (a, b) = {
            let mut a: Option<AssignedInteger<F>> = None;
            let mut b: Option<AssignedInteger<F>> = None;
            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    a = Some (integer_chip.assign_integer(&mut region, Some(ca.clone()), offset)?);
                    b = Some (integer_chip.assign_integer(&mut region, Some(cb.clone()), offset)?);
                    Ok(())
                },
            )?;
            (a.unwrap(), b.unwrap())
        };
        Ok(EccChip {config, integer_chip, a, b})
    }
}

pub trait EccInstruction<C: CurveAffine, F: FieldExt> {
    fn assign_point(&self, region: &mut Region<'_, F>, point: Point<C,F>, offset: &mut usize) -> Result<AssignedPoint<C, F>, Error>;
    fn assert_is_on_curve(&self, region: &mut Region<'_, F>, point: &AssignedPoint<C, F>, offset: &mut usize) -> Result<(), Error>;
    fn assert_equal(
        &self,
        region: &mut Region<'_, F>,
        p0: &AssignedPoint<C,F>,
        p1: &AssignedPoint<C,F>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C,F>, Error>;
    fn add(&self, region: &mut Region<'_, F>, p0: &AssignedPoint<C,F>, p1: &AssignedPoint<C,F>, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error>;
    fn double(&self, region: &mut Region<'_, F>, p: &AssignedPoint<C,F>, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error>;
    fn mul_var(&self, region: &mut Region<'_, F>, p: &AssignedPoint<C,F>, e: F, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error>;
    fn mul_fix(&self, region: &mut Region<'_, F>, p: C, e: F, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error>;
    fn multi_exp(&self, region: &mut Region<'_, F>, terms: Vec<Term<C, F>>, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error>;
    fn combine(&self, region: &mut Region<'_, F>, terms: Vec<Term<C, F>>, u: F, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error>;
}

impl<C: CurveAffine, F: FieldExt> EccInstruction<C, F> for EccChip<C, F> {
    fn assign_point(&self, region: &mut Region<'_, F>, point: Point<C,F>, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error> {
        let x = self.integer_chip.assign_integer(region, Some(point.x.clone()), offset)?.clone();
        let y = self.integer_chip.assign_integer(region, Some(point.y.clone()), offset)?.clone();
        let z = self.main_gate().assign_bit(region, Some(F::zero()), offset)?.clone();
        Ok(AssignedPoint::new(x,y,z))
    }

    fn assert_is_on_curve(&self, region: &mut Region<'_, F>, point: &AssignedPoint<C,F>, offset: &mut usize) -> Result<(), Error> {
        unimplemented!();
    }

    fn assert_equal(
        &self,
        region: &mut Region<'_, F>,
        p0: &AssignedPoint<C,F>,
        p1: &AssignedPoint<C,F>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C,F>, Error> {
        unimplemented!();
    }

    fn add(&self, region: &mut Region<'_, F>, p0: &AssignedPoint<C,F>, p1: &AssignedPoint<C,F>, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error> {
        self._add(region, p0, p1, offset)
    }

    fn double(&self, region: &mut Region<'_, F>, p: &AssignedPoint<C,F>, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error> {
        unimplemented!();
    }

    fn mul_var(&self, region: &mut Region<'_, F>, p: &AssignedPoint<C,F>, e: F, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error> {
        unimplemented!();
    }

    fn mul_fix(&self, region: &mut Region<'_, F>, p: C, e: F, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error> {
        unimplemented!();
    }

    fn multi_exp(&self, region: &mut Region<'_, F>, terms: Vec<Term<C, F>>, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error> {
        unimplemented!();
    }

    fn combine(&self, region: &mut Region<'_, F>, terms: Vec<Term<C, F>>, u: F, offset: &mut usize) -> Result<AssignedPoint<C,F>, Error> {
        unimplemented!();
    }
}

impl<C: CurveAffine, F: FieldExt> EccChip<C, F> {
    fn main_gate(&self) -> MainGate<F> {
        let main_gate_config = self.config.main_gate_config.clone();
        MainGate::<F>::new(main_gate_config)
    }
}

#[cfg(test)]
mod tests {
    use halo2::arithmetic::{CurveAffine, FieldExt, Field};
    use super::{IntegerChip, IntegerConfig, IntegerInstructions};
    use crate::circuit::AssignedValue;
    use crate::circuit::main_gate::{MainGate, MainGateConfig, MainGateInstructions};
    use crate::circuit::range::{RangeChip, RangeInstructions, RangeConfig};
    use crate::circuit::ecc::{Point, EccChip, EccInstruction, EccConfig};
    use crate::rns::{Integer, Limb, Rns};
    use halo2::circuit::{Layouter, SimpleFloorPlanner};
    use halo2::dev::MockProver;
    use halo2::plonk::{Circuit, ConstraintSystem, Error};
    use group::{Curve, prime::PrimeCurveAffine};
    use crate::NUMBER_OF_LIMBS;

    #[derive(Clone, Debug)]
    struct TestCircuitConfig {
        main_gate_config: MainGateConfig,
        integer_chip_config: IntegerConfig,
        ecc_chip_config: EccConfig,
        range_config: RangeConfig,
    }

    impl TestCircuitConfig {
        fn overflow_bit_lengths() -> Vec<usize> {
            vec![2, 3]
        }
    }

    #[derive(Default, Clone, Debug)]
    struct TestEcc<C: CurveAffine, N: FieldExt> {
        x: Point<C, N>,
        y: Point<C, N>,
        z: Point<C, N>,
        rns: Rns<C::Base, N>,
    }

    impl<C: CurveAffine, N: FieldExt> Circuit<N> for TestEcc<C, N> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
            let main_gate_config = MainGate::<N>::configure(meta);
            let overflow_bit_lengths = TestCircuitConfig::overflow_bit_lengths();
            let range_config = RangeChip::<N>::configure(meta, &main_gate_config, overflow_bit_lengths);
            let integer_chip_config = IntegerChip::<C::Base, N>::configure(meta, &range_config, &main_gate_config);
            let ecc_chip_config = EccConfig {
                main_gate_config: main_gate_config.clone(),
                integer_chip_config: integer_chip_config.clone()
            };
            TestCircuitConfig {
                range_config,
                integer_chip_config,
                main_gate_config,
                ecc_chip_config,
            }
        }

        fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<N>) -> Result<(), Error> {
            let integer_chip = IntegerChip::<C::Base, N>::new(config.integer_chip_config.clone(), self.rns.clone());

            let ecc_chip = EccChip::<C, N>::new(&mut layouter, config.ecc_chip_config, integer_chip)?;
            let offset = &mut 0;
            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let px = ecc_chip.assign_point(&mut region, self.x.clone(), offset)?;
                    let py = ecc_chip.assign_point(&mut region, self.y.clone(), offset)?;
                    let pz = ecc_chip.assign_point(&mut region, self.z.clone(), offset)?;
                    let r = ecc_chip.add(&mut region, &px, &py, offset)?;
                    ecc_chip.assert_equal(&mut region, &r, &pz, offset)?;
                    Ok(())
                },
            )?;


            let range_chip = RangeChip::<N>::new(config.range_config, self.rns.bit_len_lookup);
            #[cfg(not(feature = "no_lookup"))]
            range_chip.load_limb_range_table(&mut layouter)?;
            #[cfg(not(feature = "no_lookup"))]
            range_chip.load_overflow_range_tables(&mut layouter)?;

            Ok(())
        }
    }

    #[test]
    fn test_ecc_add_circuit() {
        use halo2::pasta::EpAffine as C;
        use halo2::pasta::Fq as Native;
        let bit_len_limb = 64;

        let rns_base = Rns::<<C as CurveAffine>::Base, Native>::construct(bit_len_limb);
        let rns_scalar = Rns::<<C as CurveAffine>::ScalarExt, Native>::construct(bit_len_limb);

        #[cfg(not(feature = "no_lookup"))]
        let k: u32 = (rns_base.bit_len_lookup + 1) as u32;
        #[cfg(feature = "no_lookup")]
        let k: u32 = 8;

        let sk = <C as CurveAffine>::ScalarExt::rand();
        let generator = <C as PrimeCurveAffine> :: generator();
        let pk = generator * sk;

        let pbase = //<C as PrimeCurveAffine> :: generator()
            pk
            .to_affine()
            .coordinates()
            .unwrap();
        let x = {
            let x = Integer::<<C as CurveAffine>::ScalarExt>::from_bytes_le(
                &pbase.x().to_bytes(), NUMBER_OF_LIMBS, bit_len_limb);
            let y = Integer::<<C as CurveAffine>::ScalarExt>::from_bytes_le(
                &pbase.y().to_bytes(), NUMBER_OF_LIMBS, bit_len_limb);
            Point::new(x, y)
        };
        let y = {
            let x = Integer::<<C as CurveAffine>::ScalarExt>::from_bytes_le(
                &pbase.x().to_bytes(), NUMBER_OF_LIMBS, bit_len_limb);
            let y = Integer::<<C as CurveAffine>::ScalarExt>::from_bytes_le(
                &pbase.y().to_bytes(), NUMBER_OF_LIMBS, bit_len_limb);
            Point::new(x, y)
        };
        let z = {
            let x = Integer::<<C as CurveAffine>::ScalarExt>::from_bytes_le(
                &pbase.x().to_bytes(), NUMBER_OF_LIMBS, bit_len_limb);
            let y = Integer::<<C as CurveAffine>::ScalarExt>::from_bytes_le(
                &pbase.y().to_bytes(), NUMBER_OF_LIMBS, bit_len_limb);
            Point::new(x, y)
        };

        let circuit = TestEcc::<C, Native> {
            x: x,
            y: y,
            z: z,
            rns: rns_base.clone(),
        };

        let prover = match MockProver::run(k, &circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };

        assert_eq!(prover.verify(), Ok(()));
    }
}


