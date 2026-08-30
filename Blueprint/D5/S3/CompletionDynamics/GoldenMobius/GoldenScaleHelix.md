# Golden Scale Helix

## Abstract

Golden completion lifts to a helix whose deck step advances one scale period and reverses orientation.

**Theorem 1.1 (Golden Scale Period pos).**

$$(0 < goldenScalePeriod).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.golden_scale_period_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden logarithmic scale period is strictly positive.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Golden Scale Period eq neg Log Multiplier).**

$$(goldenScalePeriod = -Real.log |goldenProjectiveMultiplier|).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.golden_scale_period_eq_neg_log_multiplier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic scale period is exactly the negative logarithm of the absolute golden projective multiplier.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Golden Helix Step Level).**

$$\forall state: GoldenHelixState,\\{}((goldenHelixStep state).level = state.level + 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_level` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem establishes golden helix step level in the module's typed setting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Golden Helix Step Scale Lift).**

$$\forall state: GoldenHelixState,\\{}((goldenHelixStep state).scaleLift = state.scaleLift + goldenScalePeriod).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_scaleLift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem establishes golden helix step scale lift in the module's typed setting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Golden Helix Step Orientation).**

$$\forall state: GoldenHelixState,\\{}((goldenHelixStep state).orientation = !state.orientation).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem establishes golden helix step orientation in the module's typed setting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Golden Helix Step Twice Orientation).**

$$\forall state: GoldenHelixState,\\{}((goldenHelixStep (goldenHelixStep state)).orientation = state.orientation).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_twice_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two completion turns restore the orientation sheet.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.7 (Golden Helix Step Twice Scale Lift).**

$$\forall state: GoldenHelixState,\\{}((goldenHelixStep (goldenHelixStep state)).scaleLift = state.scaleLift + 2 \times goldenScalePeriod).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_twice_scaleLift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two completion turns add exactly two golden scale periods.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.8 (Golden Helix Step Scale Lift Strict).**

$$\forall state: GoldenHelixState,\\{}(state.scaleLift < (goldenHelixStep state).scaleLift).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_scaleLift_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every completion turn strictly increases the lifted scale coordinate.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_level`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_orientation`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_scaleLift`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_scaleLift_strict`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_twice_orientation`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.goldenHelixStep_twice_scaleLift`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.golden_scale_period_eq_neg_log_multiplier`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.golden_scale_period_pos`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative](GoldenProjectiveDerivative.md)
