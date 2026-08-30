# Golden Projective Derivative

## Abstract

The golden Mobius derivative equals its projective multiplier.

**Theorem 1.1 (Golden Mobius Has Deriv At).**

$$(HasDerivAt goldenMobius goldenProjectiveMultiplier Real.goldenRatio).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.golden_mobius_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordinary differentiation gives the same multiplier as exact projective linearization.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Deriv Golden Mobius At Golden).**

$$(deriv goldenMobius Real.goldenRatio = goldenProjectiveMultiplier).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.deriv_golden_mobius_at_golden` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation of deriv at the golden fixed point.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Abs Golden Projective Multiplier).**

$$(|goldenProjectiveMultiplier| = (Real.goldenRatio^{-1}) ^2).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.abs_golden_projective_multiplier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projective multiplier has the expected positive magnitude.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Abs Golden Projective Multiplier lt One).**

$$(|goldenProjectiveMultiplier| < 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.abs_golden_projective_multiplier_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The completion derivative is a strict contraction in projective coordinates.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Linearized Golden Has Deriv At Zero).**

$$(HasDerivAt (\lambda y : \mathbb{R} \mapsto goldenProjectiveMultiplier \times y) goldenProjectiveMultiplier 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.linearized_golden_hasDerivAt_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by the golden multiplier has that derivative at zero.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.abs_golden_projective_multiplier`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.abs_golden_projective_multiplier_lt_one`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.deriv_golden_mobius_at_golden`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.golden_mobius_hasDerivAt`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.linearized_golden_hasDerivAt_zero`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization](GoldenCrossRatioLinearization.md)
