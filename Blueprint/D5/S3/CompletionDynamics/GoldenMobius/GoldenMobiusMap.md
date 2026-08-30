# Golden Mobius Map

## Abstract

The reciprocal golden Mobius map has the golden ratio and its conjugate as fixed points and preserves the positive half-line.

**Theorem 1.1 (Golden Mobius Fixed Golden).**

$$(goldenMobius Real.goldenRatio = Real.goldenRatio).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_mobius_fixed_golden` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive golden root is a fixed point.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Golden Mobius Fixed Conjugate).**

$$(goldenMobius Real.goldenConj = Real.goldenConj).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_mobius_fixed_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative conjugate golden root is the second fixed point.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Golden Fixed Points ne).**

$$(Real.goldenRatio \neq Real.goldenConj).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_fixed_points_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two fixed points are distinct.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Golden Fixed Point Gap).**

$$(Real.goldenRatio - Real.goldenConj = Real.sqrt 5).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_fixed_point_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Their oriented gap is the square root of the discriminant.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Golden Mobius pos).**

$$\forall x: \mathbb{R},\\{}(0 < x) \Rightarrow\\{}(0 < goldenMobius x).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_mobius_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive starting points remain in the positive affine chart.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Golden Projective Multiplier eq neg Conjugate Sq).**

$$(goldenProjectiveMultiplier = -(Real.goldenConj ^2)).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_projective_multiplier_eq_neg_conjugate_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projective multiplier can equivalently be read from the stable golden conjugate eigenvalue.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_fixed_point_gap`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_fixed_points_ne`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_mobius_fixed_conjugate`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_mobius_fixed_golden`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_mobius_pos`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.golden_projective_multiplier_eq_neg_conjugate_sq`
