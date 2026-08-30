# Golden Thread Blowup

## Abstract

Golden completion curves share the same completed value while their first blow-up coordinate and tangent retain the observer origin.

**Theorem 1.1 (Golden Thread Curve Zero).**

$$\forall c: \mathbb{R},\\{}(goldenThreadCurve c 0 = Real.goldenRatio).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem establishes golden thread curve zero in the module's typed setting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Golden Thread Curve Sub Golden).**

$$\forall c: \mathbb{R}, h: \mathbb{R},\\{}(1 - h \times c \neq 0) \Rightarrow\\{}(goldenThreadCurve c h - Real.goldenRatio = (h \times c) \times (Real.goldenRatio - Real.goldenConj) / (1 - h \times c)).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_sub_golden` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Difference from the completed fixed point in the inverse projective chart.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Golden Thread Curve Sub Conjugate).**

$$\forall c: \mathbb{R}, h: \mathbb{R},\\{}(1 - h \times c \neq 0) \Rightarrow\\{}(goldenThreadCurve c h - Real.goldenConj = (Real.goldenRatio - Real.goldenConj) / (1 - h \times c)).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_sub_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Difference from the conjugate fixed point in the inverse projective chart.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Golden Cross Ratio Thread Curve).**

$$\forall c: \mathbb{R}, h: \mathbb{R},\\{}(1 - h \times c \neq 0) \Rightarrow\\{}(goldenCrossRatio (goldenThreadCurve c h) = h \times c).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_cross_ratio_thread_curve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse chart recovers the prescribed projective coordinate exactly.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Golden Thread Curve Has Deriv At).**

$$\forall c: \mathbb{R},\\{}(HasDerivAt (goldenThreadCurve c) (c \times (Real.goldenRatio - Real.goldenConj)) 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse golden chart has first derivative c(φ-ψ) at completion.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Golden Thread Curve Has Deriv At Sqrt Five).**

$$\forall c: \mathbb{R},\\{}(HasDerivAt (goldenThreadCurve c) (c \times Real.sqrt 5) 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_hasDerivAt_sqrt_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tangent coefficient displays the discriminant gap sqrt 5.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.7 (Golden Thread Completion Value eq).**

$$\forall c_{1}: \mathbb{R}, c_{2}: \mathbb{R},\\{}(goldenThreadCurve c_{1} 0 = goldenThreadCurve c_{2} 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_completion_value_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two origin coefficients give the same completed value.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.8 (Golden Thread Tangent Injective).**

$$(Function.Injective (\lambda c : \mathbb{R} \mapsto c \times Real.sqrt 5)).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_tangent_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct origin coefficients give distinct completion tangents.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.9 (Golden Geometric Thread Cross Ratio).**

$$\forall c: \mathbb{R}, n: \mathbb{N},\\{}(1 - goldenProjectiveMultiplier ^{n} \times c \neq 0) \Rightarrow\\{}(goldenCrossRatio (goldenGeometricThread c n) = goldenProjectiveMultiplier ^{n} \times c).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_geometric_thread_cross_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At any depth where the inverse affine chart is defined, the blow-up coordinate is exactly c * multiplier^n.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.10 (Golden Geometric Thread Origin Recovery).**

$$\forall c: \mathbb{R}, n: \mathbb{N},\\{}(1 - goldenProjectiveMultiplier ^{n} \times c \neq 0) \Rightarrow\\{}((goldenProjectiveMultiplier^{-1}) ^{n} \times goldenCrossRatio (goldenGeometricThread c n) = c).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_geometric_thread_origin_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Since the multiplier is nonzero, renormalization recovers the origin coefficient at every finite depth.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_cross_ratio_thread_curve`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_geometric_thread_cross_ratio`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_geometric_thread_origin_recovery`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_completion_value_eq`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_hasDerivAt`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_hasDerivAt_sqrt_five`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_sub_conjugate`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_sub_golden`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_curve_zero`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.golden_thread_tangent_injective`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative](GoldenProjectiveDerivative.md)
