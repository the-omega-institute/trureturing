# Golden Projective Multiplier

## Abstract

The conjugate golden mode scales by minus the inverse golden ratio, while its ratio to the dominant mode scales by its inverse square.

**Theorem 1.1 (Golden Conjugate eq neg Inv).**

$$(Real.goldenConj = -Real.goldenRatio^{-1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.golden_conjugate_eq_neg_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient stable eigenvalue is minus the inverse golden ratio.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Stable Dominant Ratio eq Projective Multiplier).**

$$(Real.goldenConj / Real.goldenRatio = goldenProjectiveMultiplier).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.stable_dominant_ratio_eq_projective_multiplier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio of stable and dominant eigenvalues is the exact projective completion multiplier.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Projective Defect Modal Step).**

$$\forall A: \mathbb{R}, D: \mathbb{R},\\{}(A \neq 0) \Rightarrow\\{}(projectiveDefect (goldenModalStep (A, D)) = goldenProjectiveMultiplier \times projectiveDefect (A, D)).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.projective_defect_modal_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One Fibonacci modal step multiplies the normalized defect by the projective multiplier.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Projective Multiplier Of Modal Laws).**

$$\forall A: \mathbb{R}, D: \mathbb{R}, A': \mathbb{R}, D': \mathbb{R},\\{}(A \neq 0) \land (A' = Real.goldenRatio \times A) \land (D' = Real.goldenConj \times D) \Rightarrow\\{}(D' / A' = goldenProjectiveMultiplier \times (D / A)).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.projective_multiplier_of_modal_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Abstract recurrence form: ambient laws A' = φA and D' = ψD imply the projective law whenever the dominant coordinate is nonzero.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Forced Projective Step Zero).**

$$\forall theta: \mathbb{R},\\{}(forcedProjectiveStep theta 0 = goldenProjectiveMultiplier \times theta).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.forced_projective_step_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem establishes forced projective step zero in the module's typed setting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Zero State Zero Forcing).**

$$\forall forcing: \mathbb{R},\\{}(forcing = 0) \Rightarrow\\{}(forcedProjectiveStep 0 forcing = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.zero_state_zero_forcing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A vanishing state with zero forcing remains zero in one step.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.7 (Ambient And Projective Multipliers ne).**

$$(Real.goldenConj \neq goldenProjectiveMultiplier).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.ambient_and_projective_multipliers_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient stable eigenvalue and projective multiplier encode different normalization levels.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.ambient_and_projective_multipliers_ne`
- Truth anchor: `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.forced_projective_step_zero`
- Truth anchor: `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.golden_conjugate_eq_neg_inv`
- Truth anchor: `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.projective_defect_modal_step`
- Truth anchor: `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.projective_multiplier_of_modal_laws`
- Truth anchor: `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.stable_dominant_ratio_eq_projective_multiplier`
- Truth anchor: `D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.zero_state_zero_forcing`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap](../../CompletionDynamics/GoldenMobius/GoldenMobiusMap.md)
