# Cone positivity

## Abstract

Above two, the cone condition is equivalent to positive definiteness of a symmetric real matrix with two rows and two columns.

**Definition 1.1 (Root term).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm`

*Formalization.* `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root term is the absolute value of J times the square root of the radicand.

**Definition 1.2 (Cone bound).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.coneBound`

*Formalization.* `D5/S3/FluidDynamics/Cone/ConePositivity.coneBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cone bound subtracts the root term from P plus one quarter of the square of J.

**Theorem 1.3 (Nonnegative root term).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The root term is nonnegative for all real parameters.

**Theorem 1.4 (Square of the root term).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P greater than two, squaring the root term removes the square root.

**Theorem 1.5 (Quarter square bound).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm_ge_quarter`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm_ge_quarter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P greater than two, the root term is at least one quarter of the square of J.

**Theorem 1.6 (Bound by the parameter).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.coneBound_le_parameter`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.coneBound_le_parameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P greater than two, the cone bound is at most P.

**Theorem 1.7 (Bound greater than two).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.coneBound_gt_two`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.coneBound_gt_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P greater than two, the cone bound is strictly greater than two.

**Theorem 1.8 (Parameters at most two).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.relaxed_cone_of_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.relaxed_cone_of_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If P is greater than two and v is at most two, v lies strictly below the cone bound.

**Theorem 1.9 (Boundary polynomial).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.boundary_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.boundary_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cone boundary expression expands as a quadratic polynomial in v.

**Theorem 1.10 (Difference of squares).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.square_difference`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.square_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference of squares equals half of the cone boundary expression.

**Theorem 1.11 (Algebraic cone characterization).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.true_cone_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.true_cone_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above two, the cone condition is equivalent to v being less than P together with the strict quadratic inequality.

**Definition 1.12 (Cone matrix).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.coneMatrix`

*Formalization.* `D5/S3/FluidDynamics/Cone/ConePositivity.coneMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cone matrix is a symmetric real matrix with two rows and two columns.

**Theorem 1.13 (Quadratic positivity bridge).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.coneMatrix_posDef_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.coneMatrix_posDef_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above two, positive definiteness of the cone matrix is equivalent to the strict quadratic cone inequalities.

**Theorem 1.14 (Cone condition and positive definiteness).**

Lean statement: `D5/S3/FluidDynamics/Cone/ConePositivity.cone_condition_iff_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Cone/ConePositivity.cone_condition_iff_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above two, the cone condition is equivalent to positive definiteness of the cone matrix.

## References

- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.boundary_polynomial`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.coneBound`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.coneBound_gt_two`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.coneBound_le_parameter`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.coneMatrix`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.coneMatrix_posDef_iff`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.cone_condition_iff_posDef`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.relaxed_cone_of_le_two`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm_ge_quarter`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm_nonneg`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.rootTerm_sq`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.square_difference`
- Truth anchor: `D5/S3/FluidDynamics/Cone/ConePositivity.true_cone_iff`
