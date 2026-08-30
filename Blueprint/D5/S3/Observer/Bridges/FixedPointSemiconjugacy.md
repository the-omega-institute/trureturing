# Fixed Point Semiconjugacy

## Abstract

Semiconjugate bridges transport fixed points and stable fibers.

**Theorem 1.1 (Fixed Point Maps).**

$$\forall X: Type, Y: Type, bridge: X \to Y, sourceStep: X \to X, targetStep: Y \to Y, x: X,\\{}(Function.Semiconj bridge sourceStep targetStep) \land (Function.IsFixedPt sourceStep x) \Rightarrow\\{}(Function.IsFixedPt targetStep (bridge x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.fixed_point_maps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed point is transported through every semiconjugate bridge.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Fixed Point Reflects Of Injective).**

$$\forall X: Type, Y: Type, bridge: X \to Y, sourceStep: X \to X, targetStep: Y \to Y, x: X,\\{}(Function.Semiconj bridge sourceStep targetStep) \land (Function.Injective bridge) \land (Function.IsFixedPt targetStep (bridge x)) \Rightarrow\\{}(Function.IsFixedPt sourceStep x).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.fixed_point_reflects_of_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective semiconjugate bridge also reflects fixed points.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Fixed Point iff Of Injective).**

$$\forall X: Type, Y: Type, bridge: X \to Y, sourceStep: X \to X, targetStep: Y \to Y, x: X,\\{}(Function.Semiconj bridge sourceStep targetStep) \land (Function.Injective bridge) \Rightarrow\\{}(Function.IsFixedPt sourceStep x \Leftrightarrow Function.IsFixedPt targetStep (bridge x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.fixed_point_iff_of_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under an injective semiconjugacy, fixedness is exactly preserved.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Observation Fiber Forward Invariant).**

$$\forall X: Type, Y: Type, bridge: X \to Y, sourceStep: X \to X, targetStep: Y \to Y, x_{1}: X, x_{2}: X,\\{}(Function.Semiconj bridge sourceStep targetStep) \land (bridge x_{1} = bridge x_{2}) \Rightarrow\\{}(bridge (sourceStep x_{1}) = bridge (sourceStep x_{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.observation_fiber_forward_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality under the observer remains equal after one semiconjugate step.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Semiconjugacy Iterate).**

$$\forall X: Type, Y: Type, bridge: X \to Y, sourceStep: X \to X, targetStep: Y \to Y, n: \mathbb{N}, x: X,\\{}(Function.Semiconj bridge sourceStep targetStep) \Rightarrow\\{}(bridge ((sourceStep^{[n]}) x) = (targetStep^{[n]}) (bridge x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.semiconjugacy_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Semiconjugacy transports every finite iterate, not only one step.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Fixed Point Maps Across Composite).**

$$\forall X: Type, Y: Type, Z: Type, firstBridge: X \to Y, secondBridge: Y \to Z, firstStep: X \to X, secondStep: Y \to Y, thirdStep: Z \to Z, x: X,\\{}(Function.Semiconj firstBridge firstStep secondStep) \land (Function.Semiconj secondBridge secondStep thirdStep) \land (Function.IsFixedPt firstStep x) \Rightarrow\\{}(Function.IsFixedPt thirdStep ((secondBridge \circ firstBridge) x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.fixed_point_maps_across_composite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixed-point transport composes along two observer bridges.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.fixed_point_iff_of_injective`
- Truth anchor: `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.fixed_point_maps`
- Truth anchor: `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.fixed_point_maps_across_composite`
- Truth anchor: `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.fixed_point_reflects_of_injective`
- Truth anchor: `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.observation_fiber_forward_invariant`
- Truth anchor: `D5/S3/Observer/Bridges/FixedPointSemiconjugacy.semiconjugacy_iterate`
