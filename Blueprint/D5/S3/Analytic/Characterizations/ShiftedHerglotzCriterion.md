# Shifted Herglotz Criterion

## Abstract

Positive value Cayley scaling identifies Schur maps with Herglotz maps, with the ordinary-quotient premises and totalized edge cases made explicit.

**Definition 1.1 (Schur maps on the upper half-plane).**

Lean statement: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.IsSchurOnUpperHalfPlane`

*Formalization.* `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.IsSchurOnUpperHalfPlane` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Schur map is complex differentiable on the upper half-plane and has pointwise norm at most one there.

**Definition 1.2 (Herglotz maps on the upper half-plane).**

Lean statement: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.IsHerglotzOnUpperHalfPlane`

*Formalization.* `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.IsHerglotzOnUpperHalfPlane` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Herglotz map is complex differentiable on the upper half-plane and has nonnegative imaginary part there.

**Definition 1.3 (The shifted value Cayley transform).**

Lean statement: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.shiftedCayleyTransform`

*Formalization.* `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.shiftedCayleyTransform` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source transform sends u to i divided by omega times the quotient of one minus u by one plus u.

**Theorem 1.4 (Exact imaginary-part identity).**

$$\forall omega, u, \operatorname{Im}(\operatorname{shiftedCayleyTransform}(omega, u)) = \frac{1 - \operatorname{normSq}(u)}{omega \operatorname{normSq}(1 + u)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.shifted_cayley_imaginary_part` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct complex algebra expresses the imaginary part as the disk norm defect divided by the scale denominator, including totalized zeros.

**Theorem 1.5 (Strict positivity is the strict disk inequality).**

$$\forall omega, u, 0 < omega \Rightarrow \left(0 < \operatorname{Im}(\operatorname{shiftedCayleyTransform}(omega, u)) \Leftrightarrow \operatorname{norm}(u) < 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.shifted_cayley_positive_imaginary_part` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive omega, strict positivity of the imaginary part is equivalent to the strict unit-disk inequality, including at the totalized pole.

**Theorem 1.6 (Schur-Herglotz equivalence).**

$$\forall omega, \theta, \left(0 < omega \land \operatorname{NonvanishingOnUpperHalfPlane}(1 + \theta)\right) \Rightarrow \left(\operatorname{Herglotz}(\operatorname{shiftedCayleyTransform}(omega, \theta)) \Leftrightarrow \operatorname{Schur}(\theta)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.shifted_herglotz_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward direction recovers theta by the inverse Cayley quotient. The reverse direction differentiates the source quotient and uses the exact imaginary-part identity.

The source's word inner uses its preceding boundary-unitarity context. That boundary property is not true for arbitrary Schur maps and is therefore not asserted by this generic criterion.

**Theorem 1.7 (Positive scale is necessary).**

$$\operatorname{Herglotz}(\operatorname{shiftedCayleyTransform}(0, 2)) \land \left(\neg \operatorname{Schur}(\operatorname{const}(2)) \land \left(\operatorname{Schur}(\operatorname{const}(0)) \land \neg \operatorname{Herglotz}(\operatorname{shiftedCayleyTransform}(-1, 0))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.positive_scale_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At scale zero the totalized transform of the constant two is Herglotz although that constant is not Schur. At scale minus one, the constant zero is Schur but its transform is not Herglotz.

**Theorem 1.8 (Denominator nonvanishing is necessary).**

$$\operatorname{Herglotz}(\operatorname{shiftedCayleyTransform}(1, \operatorname{update}(\operatorname{const}(1), i, -1))) \land \left(\neg \operatorname{Schur}(\operatorname{update}(\operatorname{const}(1), i, -1)) \land \neg \operatorname{NonvanishingOnUpperHalfPlane}(1 + \operatorname{update}(\operatorname{const}(1), i, -1))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.denominator_nonvanishing_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing the constant one to minus one at i gives a discontinuous map. Totalized division sends both values to zero, so the Cayley image is Herglotz while the original map is not Schur.

**Theorem 1.9 (Degenerate function audit).**

$$\operatorname{Schur}(\operatorname{const}(-1)) \land \left(\neg \operatorname{NonvanishingOnUpperHalfPlane}(1 + \operatorname{const}(-1)) \land \left(\operatorname{Herglotz}(\operatorname{shiftedCayleyTransform}(1, \operatorname{const}(-1))) \land \neg \operatorname{Schur}(id)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.degenerate_function_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant minus one exposes the zero denominator and totalized quotient. The identity map fails the Schur bound at two i.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.IsHerglotzOnUpperHalfPlane`
- Truth anchor: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.IsSchurOnUpperHalfPlane`
- Truth anchor: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.degenerate_function_audit`
- Truth anchor: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.denominator_nonvanishing_is_necessary`
- Truth anchor: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.positive_scale_is_necessary`
- Truth anchor: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.shiftedCayleyTransform`
- Truth anchor: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.shifted_cayley_imaginary_part`
- Truth anchor: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.shifted_cayley_positive_imaginary_part`
- Truth anchor: `D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.shifted_herglotz_criterion`
