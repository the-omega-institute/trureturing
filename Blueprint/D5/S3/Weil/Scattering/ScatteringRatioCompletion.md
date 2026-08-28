# Scattering-Ratio Completion

## Abstract

A scattering-ratio reading and right-shift normalization uniquely recover a nonzero meromorphic function and its completed global representative.

**Theorem 1.1 (Scattering data and right normalization determine the global function).**

$$\begin{gathered}\forall F, G: \mathbb{C} \to \mathbb{C},\\{}\operatorname{NonzeroMeromorphic}\left(F\right) \land \operatorname{NonzeroMeromorphic}\left(G\right) \land\\{}\operatorname{scatteringRatio}\left(F\right) = \operatorname{scatteringRatio}\left(G\right) \land \operatorname{RightNormalized}\left(F, G\right) \Rightarrow\\{}(F = G) \land\\{}(\exists Q: \mathbb{C} \to \mathbb{C}, \operatorname{RecoveryFiber}\left(F, Q\right)) \land\\{}(\forall Q: \mathbb{C} \to \mathbb{C}, \operatorname{RecoveryFiber}\left(F, Q\right) \Rightarrow Q = F) \land\\{}(\operatorname{gaugeCompletion}\left(F\right) = F).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/ScatteringRatioCompletion.scattering_ratio_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero normal-form meromorphic functions F and G, the local reading R[F](s) is F(2s-1)/F(2s), with meromorphic quotients represented canonically at their discrete exceptional sets. RightNormalized(F,G) is exactly convergence of F/G to one along every sequence z+n.

The displayed conclusion has four separate leaves. It proves F=G, existence of a candidate in the recovery fiber, uniqueness of every such candidate, and equality of the selected gauge completion with F. Thus the existence and uniqueness content of unique recovery is not compressed into uniqueness alone.

The proof first converts equality of scattering readings into one-periodicity of the normal-form gauge F/G away from the discrete zero and pole sets, then uses meromorphic continuation to make that identity global. Periodicity and the right-shift limit force the gauge to be one. No Riemann hypothesis or other unproved conjecture is assumed.

## References

- Truth anchor: `D5/S3/Weil/Scattering/ScatteringRatioCompletion.scattering_ratio_completion`
- Dependency: [D5/S3/Analytic/Isolation/MeromorphicContinuationUniqueness](../../Analytic/Isolation/MeromorphicContinuationUniqueness.md)
