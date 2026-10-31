# A square-root cusp in the scalar extension angle

## Abstract

The scalar hyperideal extension angle has an explicit square-root cusp.

Along the positive scalar path with five entries fixed at 2 and the fourth entry equal to 17 minus epsilon, direct substitution into the first-slot hyperideal cosine gives -1 plus epsilon divided by 9. The clipped extension therefore follows the principal arccosine branch until the endpoint, where the value is pi.

The standard quadratic lower bound for cosine turns the arccosine displacement into a square-root lower bound. An explicit choice of epsilon defeats every finite linear bound in the scalar parameter. This formal result is the scalar regularity obstruction from Section 68.2; it does not assert a global face pairing, a complete length-coordinate norm estimate, or a Ricci-flow conclusion.

**Theorem 1.1 (Exact affine cosine along the scalar path).**

Lean statement: `D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz.scalarPathCosine_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz.scalarPathCosine_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The denominator radicands both reduce to 27, so the raw first-slot cosine is exactly -1+epsilon/9. This is the algebraic reduction that feeds the cusp estimate.

**Theorem 1.2 (Arccosine displacement has a square-root lower bound).**

Lean statement: `D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz.arccos_cusp_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz.arccos_cusp_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For epsilon between zero and nine, the principal arccosine of 1-epsilon/9 is at least the square root of 2 epsilon/9. The proof uses the exact cosine-arccosine identity and the pinned quadratic cosine inequality.

**Theorem 1.3 (Every finite scalar linear bound is defeated).**

Lean statement: `D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz.scalarPathAngle_gap_not_parameter_lipschitz`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz.scalarPathAngle_gap_not_parameter_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative finite K there is an epsilon in (0,1) for which the absolute angle gap from the endpoint exceeds K times epsilon divided by sqrt(255). Thus the exact scalar path has an unbounded angle-to-parameter ratio at the clipping endpoint.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz.arccos_cusp_lower_bound`
- Truth anchor: `D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz.scalarPathAngle_gap_not_parameter_lipschitz`
- Truth anchor: `D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz.scalarPathCosine_eq`
- Dependency: [D5/S3/Geometry/Hyperideal/TwoLengthAngleSum](TwoLengthAngleSum.md)
