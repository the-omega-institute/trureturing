# Crossing Discriminant Normal Form

## Abstract

The crossing discriminant is a square normal form with a unique fixed-base minimum.

**Theorem 1.1 (The square term determines the unique minimum).**

$$\forall A,B\in\mathbb{R},\ 3A^2+(A+B)^2=4A^2+2AB+B^2 \land 3A^2\leq3A^2+(A+B)^2 \land (3A^2+(A+B)^2=3A^2 \Leftrightarrow B=-A).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/CrossingNormalForm.crossing_normal_form_unique_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real A and B, the crossing discriminant with offset A+B is 3A^2+(A+B)^2. Expanding the square gives 4A^2+2AB+B^2.

The remaining square is nonnegative, so the discriminant is at least 3A^2. Equality holds exactly when A+B=0, equivalently B=-A; therefore B=-A is the unique minimizer for each fixed A.

This closes only the normal-form clause of pzg-v170 remark/27.393. It does not assert the atom's integer-surface classification, its polynomial-line description, or the five-class computational check.

Repository search found and reused PrimeForms.PropagationLegs.slotDiscriminant. Pinned-Mathlib searches found no exact theorem for the complete normal form or its unique minimum; the proof reuses add_sq, sq_nonneg, and sq_eq_zero_iff.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/CrossingNormalForm.crossing_normal_form_unique_minimum`
