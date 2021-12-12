use super::AssignedPoint;
use crate::circuit::ecc::general_ecc::{GeneralEccChip, GeneralEccInstruction};
use crate::circuit::integer::{IntegerChip, IntegerInstructions};
use crate::circuit::main_gate::{CombinationOption, MainGateColumn, MainGateInstructions, Term};
use crate::circuit::{Assigned, AssignedCondition, AssignedInteger, AssignedValue, UnassignedValue};
use crate::rns::{big_to_fe, fe_to_big};
use crate::{BIT_LEN_LIMB, NUMBER_OF_LIMBS};
use halo2::arithmetic::{CurveAffine, FieldExt};
use halo2::circuit::Region;
use halo2::plonk::Error;
use num_bigint::BigUint as big_uint;

struct ScalarTuple<F: FieldExt> {
    h: AssignedValue<F>,
    l: AssignedValue<F>,
}

struct BitHelper<F: FieldExt> {
    bits: ScalarTuple<F>,
    carry: AssignedValue<F>,
}

impl<Emulated: CurveAffine, F: FieldExt> GeneralEccChip<Emulated, F> {
    fn decompose(
        &self,
        region: &mut Region<'_, F>,
        // FIXME: input: AssignedInteger<Emulated::ScalarExt>,
        input: AssignedInteger<F>,
        offset: &mut usize,
    ) -> Result<Vec<ScalarTuple<F>>, Error> {
        let zero = big_uint::from(0 as u64);
        let one = big_uint::from(1 as u64);
        let two = big_uint::from(2 as u64);
        let four = big_uint::from(4 as u64);

        let main_gate = self.main_gate();
        let mut res = Vec::with_capacity(NUMBER_OF_LIMBS * BIT_LEN_LIMB / 2);
        let mut d = zero.clone();
        let mut carry_bits = [zero.clone(), zero.clone(), zero.clone(), zero.clone()];

        // check that x == 0 or x == 1
        let range_check = |region: &mut Region<'_, F>, assigned: AssignedValue<F>, offset: &mut usize| -> Result<(), Error> {
            main_gate.assert_bit(region, assigned, offset)?;
            Ok(())
        };

        for idx in 0..NUMBER_OF_LIMBS {
            d = d + match input.limb(idx).value() {
                Some(v) => fe_to_big(v),
                _ => zero.clone(),
            };

            for _ in 0..(BIT_LEN_LIMB / 2) {
                let current = Term::Unassigned(Some(big_to_fe(d.clone())), -F::from_u64(1));
                let mut a = zero.clone();
                let mut b = zero.clone();
                let mut carry = zero.clone();

                if d > zero {
                    let rem = &d % &four;
                    a = ((&rem) & (&two)) >> 1;
                    b = (&rem) & (&one);
                    carry = (&a) & (&b);
                    d = d - &rem + &four * &carry;
                    d = d / &four;
                }

                let a_f = big_to_fe(a);
                let b_f = big_to_fe(b);
                let carry_f = big_to_fe(carry);

                // 2a+b-4carry+4d_next = d
                let (cell_a, cell_b, cell_c, _) = main_gate.combine(
                    region,
                    Term::Unassigned(Some(a_f), F::from_u64(2)),
                    Term::Unassigned(Some(b_f), F::from_u64(1)),
                    Term::Unassigned(Some(carry_f), -F::from_u64(4)),
                    current,
                    F::zero(),
                    offset,
                    CombinationOption::CombineToNextAdd(F::from_u64(4)),
                )?;

                res.push(BitHelper {
                    bits: ScalarTuple {
                        h: AssignedValue::new(cell_a, Some(a_f)),
                        l: AssignedValue::new(cell_b, Some(b_f)),
                    },
                    carry: AssignedValue::new(cell_c, Some(carry_f)),
                })
            }

            carry_bits[idx] = d.clone();
        }

        for idx in 0..NUMBER_OF_LIMBS {
            let assigned = main_gate.assign_value(
                region,
                &UnassignedValue::new(Some(big_to_fe(carry_bits[idx].clone()))),
                MainGateColumn::A,
                offset,
            )?;
            main_gate.assert_bit(region, assigned, offset)?;
        }

        for x in res.iter() {
            range_check(region, x.bits.h.clone(), offset)?;
            range_check(region, x.bits.l.clone(), offset)?;

            // a==1 & b==1 <=> carry == 1
            main_gate.combine(
                region,
                Term::Assigned(&x.bits.h, F::zero()),
                Term::Assigned(&x.bits.l, F::zero()),
                Term::Assigned(&x.carry, -F::one()),
                Term::Zero,
                F::zero(),
                offset,
                CombinationOption::SingleLinerMul,
            )?;
        }

        Ok(res.into_iter().map(|kv| kv.bits).collect())
    }

    pub fn create_identity_point(&self, region: &mut Region<'_, F>, offset: &mut usize) -> Result<AssignedPoint<F>, Error> {
        let main_gate = self.main_gate();
        let base_chip = self.base_field_chip();

        let z = base_chip.rns.new_from_big(0u32.into());
        let z = base_chip.assign_integer(region, Some(z), offset)?;
        let c = main_gate.assign_bit(region, Some(F::one()), offset)?;
        Ok(AssignedPoint::new(z.clone(), z, c))
    }

    pub(crate) fn _mul_var(
        &self,
        region: &mut Region<'_, F>,
        p: AssignedPoint<F>,
        // FIXME: e: AssignedInteger<Emulated::ScalarExt>,
        e: AssignedInteger<F>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<F>, Error> {
        let main_gate = self.main_gate();

        let p_neg = self.negate(region, &p, offset)?;
        let p_double = self.double(region, &p, offset)?;
        let selector = self.decompose(region, e, offset)?;

        let mut point = self.create_identity_point(region, offset)?;

        for di in selector.iter().rev() {
            let a_is_zero = main_gate.is_zero(region, di.h.clone(), offset)?;
            let b_is_zero = main_gate.is_zero(region, di.l.clone(), offset)?;
            let b_is_not_zero = main_gate.cond_not(region, &b_is_zero, offset)?;
            let b1 = self.select_or_assign(region, &b_is_not_zero, &p, Emulated::identity(), offset)?;
            let b2 = self.select(region, &b_is_zero, &p_double, &p_neg, offset)?;
            let a = self.select(region, &a_is_zero, &b1, &b2, offset)?;

            // each iter handles 2bits
            point = self.double(region, &point, offset)?;
            point = self.double(region, &point, offset)?;
            point = self.add(region, &point, &a, offset)?;
        }

        Ok(point)
    }
}
