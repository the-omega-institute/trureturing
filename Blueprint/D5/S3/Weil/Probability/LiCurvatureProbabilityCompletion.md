# LiCurvatureProbabilityCompletion

## Abstract

Circle probability measures, the existing negative-power Fourier moments, and the existing Toeplitz matrices.

**Theorem 1.1 (One measure reconstructs the entire original sequence).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.normalized_curvature_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.normalized_curvature_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All normalized curvature matrices determine a unique probability measure. Existing second-difference uniqueness identifies every original coefficient with the existing geometric-polynomial energy.

**Theorem 1.2 (Constructed curvature measure implies coefficient positivity).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.normalized_curvature_forces_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.normalized_curvature_forces_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative first coefficient and the original recurrence yield positivity of every coefficient via the constructed measure.

**Theorem 1.3 (Remove the supplied Herglotz representation premise).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.li_curvature_criterion_without_herglotz`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.li_curvature_criterion_without_herglotz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization is stated explicitly. The canonical arithmetic Li criterion and RH Fourier representation remain assumptions; the common probability measure no longer does.

**Theorem 1.4 (The reverse implication only needs the time-one law).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.time_one_li_probability_implies_rh`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.time_one_li_probability_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The moment modulus bound proves nonnegative coefficients for a supplied time-one law. This consumes an explicit arithmetic Li criterion and does not assert the law exists.

## References

- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.li_curvature_criterion_without_herglotz`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.normalized_curvature_forces_nonnegative`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.normalized_curvature_reconstruction`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion.time_one_li_probability_implies_rh`
- Dependency: [D5/S3/Weil/Probability/CircleProbabilitySemigroup](CircleProbabilitySemigroup.md)
