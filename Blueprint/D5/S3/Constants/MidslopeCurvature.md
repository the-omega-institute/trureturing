# Midslope Curvature

## Abstract

The harmonic and arithmetic midslope-curvature integrals have exact values.

**Theorem 1.1 (The harmonic midslope curvature vanishes).**

$$J(-1)=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/MidslopeCurvature.J_neg_one_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The definition uses the repository's harmonic power mean in the producer-form integral. Twice that mean on the two half-scaled symmetric inputs is 1 - t^2, so the bracket and hence the full integrand vanish pointwise.

**Theorem 1.2 (The arithmetic midslope curvature is minus log two).**

$$J(1)=-\log 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/MidslopeCurvature.J_one_eq_neg_log_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the arithmetic mean on the two half-scaled symmetric inputs is one. On the open unit interval the producer integrand therefore reduces to -1 / (1 + t); endpoint-insensitive interval congruence removes the exceptional displayed endpoint values. A unit shift then turns the remaining integral into the reciprocal integral from one to two, evaluated by mathlib's logarithmic integral.

## References

- Truth anchor: `D5/S3/Constants/MidslopeCurvature.J_one_eq_neg_log_two`
- Truth anchor: `D5/S3/Constants/MidslopeCurvature.J_neg_one_eq_zero`
- Dependency: [D5/S3/Constants/PowerMeanKernel](PowerMeanKernel.md)
