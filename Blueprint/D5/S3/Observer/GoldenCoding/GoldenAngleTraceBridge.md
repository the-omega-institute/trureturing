# Golden Angle Trace Bridge

## Abstract

Rotation trace sends thirty-six degrees to the golden ratio.

**Theorem 1.1 (Thirty Six Degrees eq Golden Angle).**

$$(degreesToRadians 36 = goldenAngle).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.thirty_six_degrees_eq_golden_angle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Thirty-six degrees is exactly the golden angle in radians.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Golden Angle Trace eq Golden Ratio).**

$$(rotationTrace goldenAngle = Real.goldenRatio).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.golden_angle_trace_eq_golden_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace of the thirty-six-degree rotation is exactly the golden ratio.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Thirty Six Degree Trace eq Golden Ratio).**

$$(rotationTrace (degreesToRadians 36) = Real.goldenRatio).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.thirty_six_degree_trace_eq_golden_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Degree-valued formulation of the golden trace identity.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Rotation Trace neg).**

$$\forall theta: \mathbb{R},\\{}(rotationTrace (-theta) = rotationTrace theta).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.rotation_trace_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace observer forgets orientation.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Golden Angle ne neg).**

$$(goldenAngle \neq -goldenAngle).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.golden_angle_ne_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden angle is genuinely distinct from its reflected angle.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Rotation Trace Not Injective).**

$$(\neg Function.Injective rotationTrace).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.rotation_trace_not_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consequently the trace observer is not injective.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.7 (Golden Angle Trace Quadratic).**

$$(rotationTrace goldenAngle ^2 = rotationTrace goldenAngle + 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.golden_angle_trace_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observed trace retains the golden quadratic relation.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.8 (Golden Angle Trace Reciprocal Fixed).**

$$(1 + 1 / rotationTrace goldenAngle = rotationTrace goldenAngle).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.golden_angle_trace_reciprocal_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace also retains the reciprocal fixed-point presentation.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.golden_angle_ne_neg`
- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.golden_angle_trace_eq_golden_ratio`
- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.golden_angle_trace_quadratic`
- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.golden_angle_trace_reciprocal_fixed`
- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.rotation_trace_neg`
- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.rotation_trace_not_injective`
- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.thirty_six_degree_trace_eq_golden_ratio`
- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.thirty_six_degrees_eq_golden_angle`
