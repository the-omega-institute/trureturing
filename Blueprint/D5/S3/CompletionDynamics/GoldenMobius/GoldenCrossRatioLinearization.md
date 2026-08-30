# Golden Cross Ratio Linearization

## Abstract

Golden cross-ratio coordinates exactly linearize the Mobius map.

**Theorem 1.1 (Golden Cross Ratio At Golden).**

$$(goldenCrossRatio Real.goldenRatio = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_cross_ratio_at_golden` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem establishes golden cross ratio at golden in the module's typed setting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Golden Mobius Sub Golden).**

$$\forall x: \mathbb{R},\\{}(x \neq 0) \Rightarrow\\{}(goldenMobius x - Real.goldenRatio = -(x - Real.goldenRatio) / (Real.goldenRatio \times x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_mobius_sub_golden` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Numerator identity in a denominator-separated form.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Golden Mobius Sub Conjugate).**

$$\forall x: \mathbb{R},\\{}(x \neq 0) \Rightarrow\\{}(goldenMobius x - Real.goldenConj = Real.goldenRatio \times (x - Real.goldenConj) / x).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_mobius_sub_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Denominator identity in a denominator-separated form.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Golden Cross Ratio Linearization).**

$$\forall x: \mathbb{R},\\{}(x \neq 0) \land (x \neq Real.goldenConj) \Rightarrow\\{}(goldenCrossRatio (goldenMobius x) = goldenProjectiveMultiplier \times goldenCrossRatio x).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_cross_ratio_linearization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact golden projective linearization.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Positive Avoids Golden Singularities).**

$$\forall x: \mathbb{R},\\{}(0 < x) \Rightarrow\\{}(x \neq 0 \land x \neq Real.goldenConj).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.positive_avoids_golden_singularities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive points avoid both affine-chart singularities.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Golden Mobius Iterate pos).**

$$\forall n: \mathbb{N}, x: \mathbb{R},\\{}(0 < x) \Rightarrow\\{}(0 < (goldenMobius^{[n]}) x).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_mobius_iterate_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity is invariant under every finite Mobius iterate.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.7 (Golden Cross Ratio Iterate).**

$$\forall n: \mathbb{N}, x: \mathbb{R},\\{}(0 < x) \Rightarrow\\{}(goldenCrossRatio ((goldenMobius^{[n]}) x) = goldenProjectiveMultiplier ^{n} \times goldenCrossRatio x).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_cross_ratio_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact geometric contraction law on the positive affine chart.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_cross_ratio_at_golden`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_cross_ratio_iterate`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_cross_ratio_linearization`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_mobius_iterate_pos`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_mobius_sub_conjugate`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.golden_mobius_sub_golden`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.positive_avoids_golden_singularities`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap](GoldenMobiusMap.md)
