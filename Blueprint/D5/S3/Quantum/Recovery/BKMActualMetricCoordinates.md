# Euclidean coordinates for the finite BKM metric

## Abstract

Invertible Euclidean coordinates for the finite BKM form and order of the relative operator.

**Theorem 1.1 (Positive definite BKM coefficient).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.omegaCoefficient_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.omegaCoefficient_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of a positive definite input is positive definite. Compare the input to a positive multiple of the identity and use the coefficient of the identity.

**Definition 1.2 (Relative operator).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator`

*Formalization.* `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In Euclidean coordinates the coefficient of a is conjugated by the inverse square root of the coefficient of b.

**Theorem 1.3 (Self-adjoint relative operator).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator_selfAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of the coefficient of a is preserved by conjugation with the self-adjoint inverse square root.

**Theorem 1.4 (Relative operator sandwich).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under ℓb ≤ a ≤ ub for positive definite a and b and 0 < ℓ ≤ u, the relative operator lies between ℓI and uI. Conjugation turns the reference coefficient into the identity.

**Definition 1.5 (Invertible BKM coordinates).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.metricCoordinates`

*Formalization.* `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.metricCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vectorize a matrix and apply the positive square root of the BKM coefficient. Its inverse uses the inverse square root and inverse vectorization.

**Definition 1.6 (Observable BKM form).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.bkmInner`

*Formalization.* `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.bkmInner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observable form on X and Y is the trace of X* times the BKM power integral applied to Y.

**Theorem 1.7 (Realization of the BKM inner product).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.metricCoordinates_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.metricCoordinates_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Euclidean inner product of the coordinates equals the observable BKM form at the reference input.

**Theorem 1.8 (Realization of the second BKM form).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the coordinates for b, insertion of the relative operator gives the observable BKM form at a.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.bkmInner`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.metricCoordinates`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.metricCoordinates_inner`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.omegaCoefficient_posDef`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator_bounds`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator_inner`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricCoordinates.relativeOperator_selfAdjoint`
- Dependency: [D5/S3/Quantum/Recovery/BKMRelativeDensity](BKMRelativeDensity.md)
