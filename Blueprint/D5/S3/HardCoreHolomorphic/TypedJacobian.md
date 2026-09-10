# TypedJacobian

## Abstract

Explicit holomorphic hard-core coordinates and uniform complex neighborhoods.

**Definition 1.1 (messageProduct).**

Lean statement: `D5/S3/HardCoreHolomorphic/TypedJacobian.messageProduct`

*Formalization.* `D5/S3/HardCoreHolomorphic/TypedJacobian.messageProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Product over precisely the retained children; an empty product is one.

**Definition 1.2 (logArgument).**

Lean statement: `D5/S3/HardCoreHolomorphic/TypedJacobian.logArgument`

*Formalization.* `D5/S3/HardCoreHolomorphic/TypedJacobian.logArgument` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The single log argument. It is positive on the real box and has no vanishing issue at activity zero, where it equals b0-a0.

**Definition 1.3 (rowMap).**

Lean statement: `D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap`

*Formalization.* `D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual transformed hard-core map. There is no logarithm of the activity.

**Definition 1.4 (jacobianEntry).**

Lean statement: `D5/S3/HardCoreHolomorphic/TypedJacobian.jacobianEntry`

*Formalization.* `D5/S3/HardCoreHolomorphic/TypedJacobian.jacobianEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coefficients of the full differential in the child coordinates.

**Definition 1.5 (activityEntry).**

Lean statement: `D5/S3/HardCoreHolomorphic/TypedJacobian.activityEntry`

*Formalization.* `D5/S3/HardCoreHolomorphic/TypedJacobian.activityEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coefficient of activity variation in the same differential.

**Theorem 1.6 (rowMap hasDerivAt).**

Lean statement: `D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative along every differentiable complex input curve. Since both activity and all child tangent values are arbitrary, this identifies the full Jacobian, including mixed simultaneous input perturbations and all pruning sets.

**Theorem 1.7 (rowMap differentiableAt).**

Lean statement: `D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap_differentiableAt`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap_differentiableAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Joint holomorphy of the actual finite-dimensional map on its pole-free principal-log domain; it is not inferred just from a pointwise Jacobian fit.

**Theorem 1.8 (inverse rowMap).**

Lean statement: `D5/S3/HardCoreHolomorphic/TypedJacobian.inverse_rowMap`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/TypedJacobian.inverse_rowMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inverse coordinates return the actual vacancy recursion. Both possible rational poles are stated; the quantitative tube later excludes them uniformly.

**Theorem 1.9 (jacobian vacancy identity).**

Lean statement: `D5/S3/HardCoreHolomorphic/TypedJacobian.jacobian_vacancy_identity`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/TypedJacobian.jacobian_vacancy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Jacobian entry is exactly the previously certified message ratio. This is a rational identity; no assumed derivative identification is used.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/TypedJacobian.activityEntry`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TypedJacobian.inverse_rowMap`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TypedJacobian.jacobianEntry`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TypedJacobian.jacobian_vacancy_identity`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TypedJacobian.logArgument`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TypedJacobian.messageProduct`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap_differentiableAt`
- Truth anchor: `D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap_hasDerivAt`
- Dependency: [D5/S3/HardCoreHolomorphic/AffineChart](AffineChart.md)
