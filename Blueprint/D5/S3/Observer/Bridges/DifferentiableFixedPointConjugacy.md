# Differentiable Fixed Point Conjugacy

## Abstract

Nondegenerate differentiable bridges preserve local multipliers.

**Theorem 1.1 (Derivative Intertwining At Fixed Point).**

$$\forall bridge: \mathbb{R} \to \mathbb{R}, sourceStep: \mathbb{R} \to \mathbb{R}, targetStep: \mathbb{R} \to \mathbb{R}, x: \mathbb{R}, dBridge: \mathbb{R}, dSource: \mathbb{R}, dTarget: \mathbb{R},\\{}(Function.Semiconj bridge sourceStep targetStep) \land (Function.IsFixedPt sourceStep x) \land (HasDerivAt bridge dBridge x) \land (HasDerivAt sourceStep dSource x) \land (HasDerivAt targetStep dTarget (bridge x)) \Rightarrow\\{}(dBridge \times dSource = dTarget \times dBridge).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.derivative_intertwining_at_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chain rule intertwines the two local multipliers at a fixed point.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Multiplier eq Of Nondegenerate Bridge).**

$$\forall bridge: \mathbb{R} \to \mathbb{R}, sourceStep: \mathbb{R} \to \mathbb{R}, targetStep: \mathbb{R} \to \mathbb{R}, x: \mathbb{R}, dBridge: \mathbb{R}, dSource: \mathbb{R}, dTarget: \mathbb{R},\\{}(Function.Semiconj bridge sourceStep targetStep) \land (Function.IsFixedPt sourceStep x) \land (HasDerivAt bridge dBridge x) \land (HasDerivAt sourceStep dSource x) \land (HasDerivAt targetStep dTarget (bridge x)) \land (dBridge \neq 0) \Rightarrow\\{}(dSource = dTarget).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.multiplier_eq_of_nondegenerate_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero bridge derivative forces equality of local multipliers.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Attracting Multiplier iff).**

$$\forall bridge: \mathbb{R} \to \mathbb{R}, sourceStep: \mathbb{R} \to \mathbb{R}, targetStep: \mathbb{R} \to \mathbb{R}, x: \mathbb{R}, dBridge: \mathbb{R}, dSource: \mathbb{R}, dTarget: \mathbb{R},\\{}(Function.Semiconj bridge sourceStep targetStep) \land (Function.IsFixedPt sourceStep x) \land (HasDerivAt bridge dBridge x) \land (HasDerivAt sourceStep dSource x) \land (HasDerivAt targetStep dTarget (bridge x)) \land (dBridge \neq 0) \Rightarrow\\{}(|dSource| < 1 \Leftrightarrow |dTarget| < 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.attracting_multiplier_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict attraction is preserved by a nondegenerate bridge.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Neutral Multiplier iff).**

$$\forall bridge: \mathbb{R} \to \mathbb{R}, sourceStep: \mathbb{R} \to \mathbb{R}, targetStep: \mathbb{R} \to \mathbb{R}, x: \mathbb{R}, dBridge: \mathbb{R}, dSource: \mathbb{R}, dTarget: \mathbb{R},\\{}(Function.Semiconj bridge sourceStep targetStep) \land (Function.IsFixedPt sourceStep x) \land (HasDerivAt bridge dBridge x) \land (HasDerivAt sourceStep dSource x) \land (HasDerivAt targetStep dTarget (bridge x)) \land (dBridge \neq 0) \Rightarrow\\{}(|dSource| = 1 \Leftrightarrow |dTarget| = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.neutral_multiplier_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Neutrality is preserved by a nondegenerate bridge.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Repelling Multiplier iff).**

$$\forall bridge: \mathbb{R} \to \mathbb{R}, sourceStep: \mathbb{R} \to \mathbb{R}, targetStep: \mathbb{R} \to \mathbb{R}, x: \mathbb{R}, dBridge: \mathbb{R}, dSource: \mathbb{R}, dTarget: \mathbb{R},\\{}(Function.Semiconj bridge sourceStep targetStep) \land (Function.IsFixedPt sourceStep x) \land (HasDerivAt bridge dBridge x) \land (HasDerivAt sourceStep dSource x) \land (HasDerivAt targetStep dTarget (bridge x)) \land (dBridge \neq 0) \Rightarrow\\{}(1 < |dSource| \Leftrightarrow 1 < |dTarget|).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.repelling_multiplier_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Repulsion is preserved by a nondegenerate bridge.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.attracting_multiplier_iff`
- Truth anchor: `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.derivative_intertwining_at_fixed_point`
- Truth anchor: `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.multiplier_eq_of_nondegenerate_bridge`
- Truth anchor: `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.neutral_multiplier_iff`
- Truth anchor: `D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.repelling_multiplier_iff`
- Dependency: [D5/S3/Observer/Bridges/FixedPointSemiconjugacy](FixedPointSemiconjugacy.md)
