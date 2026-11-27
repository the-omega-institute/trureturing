# Large roots of the exact fixed-perturbation integer clock

## Abstract

The perturbed integer clock has a unique large root within one of its unperturbed reference.

**Theorem 1.1 (Equivalence with the exact price equation).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock.inverseClock_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock.inverseClock_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every nonnegative integer height and positive price, the logarithmic inverse clock equals that height precisely when the perturbed price equals the target price. The target uses the integer exponent and the literal subtraction by two.

**Theorem 1.2 (The large roots exist and diverge).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock.exists_fixedB_integerClock`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock.exists_fixedB_integerClock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unperturbed clock is the positive inverse of the continuous strictly increasing map L to L times exp L at the corresponding reciprocal price. With a fixed real perturbation and positive decay exponent, the relative price factor tends to one. This brackets all late roots within one of the unperturbed clock, and the normalized price derivative is eventually negative, giving uniqueness beyond a fixed positive threshold.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock.exists_fixedB_integerClock`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock.inverseClock_eq_iff`
