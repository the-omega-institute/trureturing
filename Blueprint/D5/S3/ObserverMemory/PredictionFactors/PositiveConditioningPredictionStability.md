# Positive Conditioning Preserves Predictive Equivalence

## Abstract

Equal discrete future laws remain equal after conditioning on a positive next outcome.

**Theorem 1.1 (Predictive equivalence survives positive conditioning).**

$$\begin{gathered}\forall H, A, Y, W, Z: \operatorname{Type},\\{}\operatorname{Finite}\left(Z\right),\\{}J: H \to \left(A \to \left(W \to \left(Y \times Z \to \mathbb{R}\right)\right)\right),\\{}p: H \to \left(A \to \left(Y \to \mathbb{R}\right)\right),\\{}K: H \to \left(W \to \left(Z \to \mathbb{R}\right)\right),\\{}e: H \to \left(A \to \left(Y \to H\right)\right),\\{}(\forall h: H, a: A, w: W, \operatorname{marginal}\left(J(h, a, w)\right) = p(h, a)) \land\\{}(\forall h: H, a: A, y: Y, w: W, z: Z,\\{}K(e(h, a, y), w, z) = \operatorname{conditional}\left(J(h, a, w), y, z\right)) \Rightarrow\\{}\forall h, h': H, a: A, y: Y,\\{}(\forall a': A, w: W, J(h, a', w) = J(h', a', w)) \land 0 < p(h, a, y) \Rightarrow\\{}\forall w: W, K(e(h, a, y), w) = K(e(h', a, y), w).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/PositiveConditioningPredictionStability.predictive_equivalence_preserved_by_positive_conditioning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A history, action, and future protocol determine a finite joint law of the next observation and the remaining future record. Its first-coordinate marginal is the next-observation law.

The history-extension equation identifies every future law after an observed outcome with the repository's canonical conditional of that joint law.

Equal predictive profiles give equal numerators and denominators. Positive outcome mass makes both denominators nonzero, so the conditional future laws agree for every later protocol.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/PositiveConditioningPredictionStability.predictive_equivalence_preserved_by_positive_conditioning`
- Dependency: [D5/S3/Divergence/ChainRule](../../Divergence/ChainRule.md)
