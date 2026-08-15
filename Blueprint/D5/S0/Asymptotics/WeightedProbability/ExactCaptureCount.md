# Exact Capture Count Distribution

## Abstract

Every finite capture-count value has an exact alternating-sum product mass.

**Theorem 1.1 (Exact mass of j captured addresses).**

$$\forall j\in \mathbb{N},\ (\forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow \operatorname{eventProbability}\left(q, \{s \mid \lvert \{a\in A \mid \operatorname{Captured}\left(f, s, a\right)\} \rvert = j\}\right) = \sum_{S\subseteq A, \lvert S \rvert=j} \sum_{U\subseteq {A\setminus S}} (-1)^{\lvert U \rvert} \prod_{b\in A} \operatorname{if}\left(b\in \operatorname{union}\left(S, U\right), \operatorname{fixedPowerMass}\left(q, f, b, \lvert \operatorname{union}\left(S, U\right) \rvert\right), \operatorname{collisionPowerMass}\left(q, f, b, \lvert \operatorname{union}\left(S, U\right) \rvert\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/ExactCaptureCount.exact_capture_count_probability` (`✓ std3`). ∎

*Citation.* Gerald Berman and K. D. Fryer (1972). *The Inclusion-Exclusion Principle*. DOI: [10.1016/b978-0-12-092750-0.50008-9](https://doi.org/10.1016/b978-0-12-092750-0.50008-9).

*Commentary.*

Samples with capture count j are partitioned by their exact set S of addresses satisfying the frozen Captured predicate.

For each S, complement inclusion-exclusion over addresses outside S gives the alternating sum over U. The imported exact prescribed-set law evaluates every S union U intersection as the displayed product.

No nonnegativity premise is needed. Normalization is used only by the existing exact product-mass theorem.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/ExactCaptureCount.exact_capture_count_probability`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion](FiniteInclusionExclusion.md)
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture](FiniteProductSetCapture.md)
