# Scattering-Ratio Completion

## Abstract

A scattering-ratio reading and right-shift normalization uniquely recover a nonzero meromorphic function and its completed global representative.

**Theorem 1.1 (Scattering data and right normalization determine the global function).**

$$\begin{gathered}\forall F, G: \mathbb{C} \to \mathbb{C},\\{}\operatorname{NonzeroMeromorphic}\left(F\right) \land \operatorname{NonzeroMeromorphic}\left(G\right) \land\\{}\operatorname{scatteringRatio}\left(F\right) = \operatorname{scatteringRatio}\left(G\right) \land \operatorname{RightNormalized}\left(F, G\right) \Rightarrow\\{}N_{G}(Q) := \operatorname{RightNormalized}\left(Q, G\right),\\{}(F = G) \land\\{}(\exists Q: \mathbb{C} \to \mathbb{C}, \operatorname{RecoveryFiber}\left(\operatorname{scatteringRatio}\left(G\right), N_{G}, Q\right)) \land\\{}(\forall Q: \mathbb{C} \to \mathbb{C}, \operatorname{RecoveryFiber}\left(\operatorname{scatteringRatio}\left(G\right), N_{G}, Q\right) \Rightarrow Q = F) \land\\{}(\operatorname{gaugeCompletion}\left(\operatorname{scatteringRatio}\left(G\right), N_{G}\right) = F).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/ScatteringRatioCompletion.scattering_ratio_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero normal-form meromorphic functions F and G, the local reading R[F](s) is F(2s-1)/F(2s), with meromorphic quotients represented canonically at their discrete exceptional sets. RightNormalized(F,G) is exactly convergence of F/G to one along every sequence z+n.

Write N_G(Q) for RightNormalized(Q,G). The completion operator receives only the local reading R[G] and this normalization predicate. Its recovery fiber is inhabited by G, while the target F occurs only as the recovered output after the two source hypotheses prove F=G.

The displayed conclusion has four separate leaves: F=G, existence in the data-indexed recovery fiber, uniqueness there, and equality of the selected gauge completion with F. Thus unique recovery is not compressed into uniqueness alone.

The proof first converts equality of scattering readings into one-periodicity of the normal-form gauge F/G away from the discrete zero and pole sets, then uses meromorphic continuation to make that identity global. Periodicity and the right-shift limit force the gauge to be one. No Riemann hypothesis or other unproved conjecture is assumed.

## References

- Truth anchor: `D5/S3/Weil/Scattering/ScatteringRatioCompletion.scattering_ratio_completion`
- Dependency: [D5/S3/Analytic/Isolation/MeromorphicContinuationUniqueness](../../Analytic/Isolation/MeromorphicContinuationUniqueness.md)
