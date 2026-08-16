# The Quadratic Base Beta13

## Abstract

The quadratic base beta13 has a conjugate outside the open unit disk.

**Theorem 1.1 (Beta13 satisfies its quadratic equation).**

$$\mathit{beta13}^{2} = \mathit{beta13} + 3$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13.beta13_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squaring the radical definition and using sqrt(13)^2 = 13 gives beta13 squared equal to beta13 plus three.

**Theorem 1.2 (The conjugate lies outside the unit disk).**

$$\left|\mathit{beta13Conjugate}\right| > 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13.beta13_conjugate_abs_gt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugate is negative, and sqrt(13) is greater than three, so its absolute value is strictly greater than one.

**Theorem 1.3 (Beta13 is irrational).**

$$\operatorname{Irrational}\left(\mathit{beta13}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13.beta13_irrational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's irrationality theorem for the square root of a prime passes through the nonzero rational affine transformation.

## References

- Truth anchor: `D5/S0/Tower/NonPisot/Beta13.beta13_conjugate_abs_gt_one`
- Truth anchor: `D5/S0/Tower/NonPisot/Beta13.beta13_irrational`
- Truth anchor: `D5/S0/Tower/NonPisot/Beta13.beta13_sq`
