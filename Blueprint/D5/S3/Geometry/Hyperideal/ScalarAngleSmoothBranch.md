# Smooth raw cosine versus singular clipped angle

## Abstract

The raw scalar cosine branch is smooth while its clipped angle has an endpoint cusp.

On the length slice used in Section 68, the first-slot raw cosine is the elementary function (8-cosh(s))/9. It is differentiable for every real length parameter. The preceding cusp theorem shows that applying the clipped arccosine at the endpoint still defeats every finite scalar linear bound.

This separates the smoothness of the raw cosine from the endpoint behavior of the extension angle. It is a scalar regularity statement only: it does not assert a global face pairing, a global curvature field, a complete flow theorem, or a uniqueness result.

**Theorem 1.1 (Exact raw cosine on the length slice).**

Lean statement: `D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.scalarLengthRawCosine_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.scalarLengthRawCosine_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six-variable formula reduces exactly to (8-cosh(s))/9 when the varying slot is the fourth coordinate and the other five coordinates are fixed at 2.

**Theorem 1.2 (The raw scalar cosine is differentiable).**

Lean statement: `D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.scalarLengthRawCosine_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.scalarLengthRawCosine_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiability follows from the exact reduction and the standard differentiability of the hyperbolic cosine.

**Theorem 1.3 (Smooth raw branch with an unbounded clipped-angle ratio).**

Lean statement: `D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.smooth_raw_branch_but_angle_not_parameter_lipschitz`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.smooth_raw_branch_but_angle_not_parameter_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The combined theorem places the differentiable raw branch beside the previously proved endpoint cusp: for every finite nonnegative K, some epsilon in (0,1) has an angle gap larger than K times epsilon divided by sqrt(255).

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.scalarLengthRawCosine_differentiable`
- Truth anchor: `D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.scalarLengthRawCosine_eq`
- Truth anchor: `D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.smooth_raw_branch_but_angle_not_parameter_lipschitz`
- Dependency: [D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz](ScalarAngleNonLipschitz.md)
