# Finite BKM heat compression

## Abstract

Finite BKM compressions of one physical heat evolution have a factored two-step defect difference.

**Definition 1.1 (Projection for a coercive form).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.relativeProjection`

*Formalization.* `D5/S3/Quantum/Recovery/BKMActualMetricHeat.relativeProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a finite-dimensional complex Hilbert space, compress a coefficient Z to the visible subspace. Its strictly positive lower operator bound makes the Gram compression injective and hence invertible. Applying its inverse to P Z gives the relative projection into that same subspace.

**Theorem 1.2 (Visible vectors are fixed).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.relativeProjection_fix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMActualMetricHeat.relativeProjection_fix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applied to a visible vector, the right-hand side of the Gram equation is exactly the Gram compression of that vector.

**Theorem 1.3 (Orthogonality of the residual).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.relativeProjection_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMActualMetricHeat.relativeProjection_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gram equation says that the coefficient applied to the residual is orthogonal to every visible vector.

**Definition 1.4 (One physical visible subspace).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.visibleCoordinates`

*Formalization.* `D5/S3/Quantum/Recovery/BKMActualMetricHeat.visibleCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reference square-root coordinate map sends the physical matrix subspace B onto V. Both compressions use V.

**Definition 1.5 (Projection for the changed BKM form).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.changedProjection`

*Formalization.* `D5/S3/Quantum/Recovery/BKMActualMetricHeat.changedProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the relative BKM operator as the coefficient Z. The density sandwich supplies the positive lower bound in reference coordinates. Pulling the projection back to matrix space gives a residual that pairs to zero with every member of B in the BKM form at a, by the Gram equation and the relative BKM operator identity.

**Definition 1.6 (Generator in reference coordinates).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.referenceGenerator`

*Formalization.* `D5/S3/Quantum/Recovery/BKMActualMetricHeat.referenceGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate the bounded physical generator L by the square-root coordinates of b.

**Theorem 1.7 (Physical heat defect identity and bound).**

Lean statement: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.bkm_heat_defect_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BKMActualMetricHeat.bkm_heat_defect_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be positive definite matrices with l b ≤ a ≤ u b and 0 < l ≤ u. For a complex matrix subspace B, work on its image V in the square-root coordinates of b. Write P for the reference orthogonal projection and R for the projection induced by the BKM form at a. Both are maps into V.

For any bounded complex-linear physical generator L and real time t, use its single conjugate in the reference coordinates to define the operators T at time t and T₂ at time 2t. With i the inclusion of V, define E = R T i and E₀ = P T i. The defect difference is the two-step defect of R minus that of P.

$D = (R \circ T_{2} \circ i - E^{2}) - (P \circ T_{2} \circ i - E_{0}^{2})$

Let K be the restriction of R to the reference orthogonal complement, W the hidden-to-hidden block of T, and C its visible-to-hidden block. For every complex scalar c, the difference satisfies the following identity and estimate in operator norms induced by the reference BKM form.

$D = (K \circ W - E \circ K) \circ C$

$\left\lVert D \right\rVert \leq \frac{u - l}{2 \cdot \sqrt{u \cdot l}} \cdot (\left\lVert W - c \cdot I \right\rVert + \left\lVert E - c \cdot I \right\rVert) \cdot \left\lVert C \right\rVert$

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.bkm_heat_defect_comparison`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.changedProjection`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.referenceGenerator`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.relativeProjection`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.relativeProjection_fix`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.relativeProjection_orthogonal`
- Truth anchor: `D5/S3/Quantum/Recovery/BKMActualMetricHeat.visibleCoordinates`
- Dependency: [D5/S3/HilbertOperators/TwoStepDefectComparison](../../HilbertOperators/TwoStepDefectComparison.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMActualMetricCoordinates](BKMActualMetricCoordinates.md)
