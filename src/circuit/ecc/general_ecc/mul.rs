use super::AssignedPoint;
use crate::circuit::ecc::general_ecc::{GeneralEccChip, GeneralEccInstruction};
use crate::circuit::AssignedInteger;
use halo2::arithmetic::{CurveAffine, FieldExt};
use halo2::circuit::Region;
use halo2::plonk::Error;
use halo2arith::AssignedValue;
use halo2arith::{
    halo2,
    utils::{big_to_fe, fe_to_big},
    Assigned, AssignedCondition, CombinationOptionCommon, MainGateInstructions, Term,
};
use num_bigint::BigUint as big_uint;
use num_integer::Integer;

struct ScalarTuple<F: FieldExt> {
    h: AssignedCondition<F>,
    l: AssignedCondition<F>,
}

impl<Emulated: CurveAffine, F: FieldExt> GeneralEccChip<Emulated, F> {
    fn decompose_value(
        &self,
        region: &mut Region<'_, F>,
        input: &dyn Assigned<F>,
        init_rem: Option<AssignedCondition<F>>,
        len: usize,
        offset: &mut usize,
    ) -> Result<(AssignedCondition<F>, Vec<ScalarTuple<F>>), Error> {
        let zero = F::zero();
        let one = F::one();
        let two = F::from(2u64);
        let four = F::from(4u64);
        let main_gate = self.main_gate();

        let mut res = vec![];

        // | A   | B   | C     | D  |
        // | --- | --- | ----- | -- |
        // | lb0 | hb0 | input | 0  |
        // | lb1 | hb1 | 0     | d1 |
        // | lb2 | hb2 | 0     | d2 |
        // ...
        // | 0   | 0   | 0     | 0 |
        assert!(len % 2 == 0);
        let len = len / 2;
        let input_value = input.value().unwrap_or(zero);
        let init_rem_value = init_rem.clone().map_or(zero, |assigned| assigned.value().unwrap_or(zero));
        let mut rem = fe_to_big(input_value + init_rem_value);

        for i in 0..len {
            let shift = |rem: big_uint, carry| {
                if rem.is_odd() {
                    (rem >> 1u64, one, carry)
                } else {
                    (rem >> 1u64, zero, 0u64)
                }
            };

            let carry = 1u64;
            let (rem_shifted, a, carry) = shift(rem.clone(), carry);
            let (rem_shifted, b, carry) = shift(rem_shifted, carry);
            let next_rem = rem_shifted + carry;

            let (l, h, _, _, _) = main_gate.combine(
                region,
                [
                    Term::Unassigned(Some(a), one),
                    Term::Unassigned(Some(b), two),
                    if i == 0 { Term::Assigned(input, -one) } else { Term::Zero },
                    Term::Zero,
                    if i == 0 {
                        match init_rem {
                            Some(_) => Term::Assigned(init_rem.as_ref().unwrap(), -one),
                            _ => Term::Zero,
                        }
                    } else {
                        Term::Unassigned(Some(big_to_fe(rem)), -one)
                    },
                ],
                zero,
                offset,
                CombinationOptionCommon::CombineToNextScaleMul(four, -four).into(),
            )?;

            res.push(ScalarTuple { h: h.into(), l: l.into() });
            rem = next_rem;
        }
        /* Set final rem also assert that it equals to zero. */
        let (_, _, _, _, carry) = main_gate.combine(
            region,
            [Term::Zero, Term::Zero, Term::Zero, Term::Zero, Term::Unassigned(Some(big_to_fe(rem)), zero)],
            zero,
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        /* Assert bit foreach a b */
        for x in res.iter() {
            main_gate.assert_bit(region, x.h.clone(), offset)?;
            main_gate.assert_bit(region, x.l.clone(), offset)?;
        }
        main_gate.assert_bit(region, carry.clone(), offset)?;

        Ok((carry.into(), res))
    }

    fn decompose_integer(
        &self,
        region: &mut Region<'_, F>,
        input: &AssignedInteger<F>,
        offset: &mut usize,
    ) -> Result<(AssignedCondition<F>, Vec<ScalarTuple<F>>), Error> {
        let mut decomposed = vec![];

        let rem = input
            .limbs
            .iter()
            .fold(Ok(None), |rem, limb| -> Result<Option<AssignedCondition<F>>, Error> {
                let rem = rem?;
                let (rem, mut limb_decomposed) = self.decompose_value(region, limb, rem, input.bit_len_limb, offset)?;
                decomposed.append(&mut limb_decomposed);
                Ok(Some(rem))
            })?
            .unwrap();

        Ok((rem, decomposed))
    }

    pub(crate) fn _mul_integer(
        &self,
        region: &mut Region<'_, F>,
        p: &AssignedPoint<F>,
        e: &AssignedInteger<F>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<F>, Error> {
        let p_neg = self.neg(region, &p, offset)?;
        let p_double = self.double(region, &p, offset)?;
        let (rem, selector) = self.decompose_integer(region, &e, offset)?;
        let mut acc = self.select_or_assign(region, &rem, &p, Emulated::identity(), offset)?;

        for di in selector.iter().rev() {
            // 0b01 - p, 0b00 - identity
            let b0 = self.select_or_assign(region, &di.l, &p, Emulated::identity(), offset)?;
            // 0b11 - p_neg, 0b10 - p_double
            let b1 = self.select(region, &di.l, &p_neg, &p_double, offset)?;
            let a = self.select(region, &di.h, &b1, &b0, offset)?;

            acc = self.double(region, &acc, offset)?;
            acc = self.double(region, &acc, offset)?;
            acc = self.add(region, &acc, &a, offset)?;
        }

        Ok(acc)
    }

    pub(crate) fn _mul_native(
        &self,
        region: &mut Region<'_, F>,
        p: &AssignedPoint<F>,
        e: &AssignedValue<F>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<F>, Error> {
        let len = ((F::NUM_BITS + 1) / 2) as usize;
        let p_neg = self.neg(region, &p, offset)?;
        let p_double = self.double(region, &p, offset)?;
        let (rem, selector) = self.decompose_value(region, &e, None, len, offset)?;
        let mut acc = self.select_or_assign(region, &rem, &p, Emulated::identity(), offset)?;

        for di in selector.iter().rev() {
            // 0b01 - p, 0b00 - identity
            let b0 = self.select_or_assign(region, &di.l, &p, Emulated::identity(), offset)?;
            // 0b11 - p_neg, 0b10 - p_double
            let b1 = self.select(region, &di.l, &p_neg, &p_double, offset)?;
            let a = self.select(region, &di.h, &b1, &b0, offset)?;

            acc = self.double(region, &acc, offset)?;
            acc = self.double(region, &acc, offset)?;
            acc = self.add(region, &acc, &a, offset)?;
        }

        Ok(acc)
    }
}
