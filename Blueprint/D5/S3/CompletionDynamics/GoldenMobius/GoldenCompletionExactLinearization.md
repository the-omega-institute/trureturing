# Golden Completion Exact Linearization

## Abstract

Golden cross-ratio linearization extends exactly through every defined finite iterate.

**Theorem 1.1 (Exact Linearization at Every Finite Depth).**

$$(\forall x: \mathbb{R},\\{}(x \neq 0) \land (x \neq Real.goldenConj) \Rightarrow\\{}(\operatorname{goldenCrossRatio}\left(\operatorname{goldenMobius}\left(x\right)\right) = goldenProjectiveMultiplier \times \operatorname{goldenCrossRatio}\left(x\right))) \land\\{}(\forall n: \mathbb{N}, x: \mathbb{R},\\{}(\forall k: \mathbb{N}, k < n \Rightarrow ((goldenMobius^{[k]}) x \neq 0 \land (goldenMobius^{[k]}) x \neq Real.goldenConj)) \Rightarrow\\{}(\operatorname{goldenCrossRatio}\left((goldenMobius^{[n]}) x\right) = goldenProjectiveMultiplier ^{n} \times \operatorname{goldenCrossRatio}\left(x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenCompletionExactLinearization.golden_completion_exact_linearization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first clause gives the exact one-step cross-ratio multiplier on the real affine chart. The second gives the exact multiplier power for every finite iterate whose earlier orbit points remain in that chart.

The map, cross-ratio coordinate, and multiplier are the canonical objects from the GoldenMobius family; the domain premises exclude only their displayed affine-chart poles.

## References

- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenCompletionExactLinearization.golden_completion_exact_linearization`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization](GoldenCrossRatioLinearization.md)
