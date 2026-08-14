# Finite Bonferroni Escape Bounds

## Abstract

Nonnegative normalized finite capture events satisfy the first- and second-order escape bounds.

**Theorem 1.1 (Two-sided weighted escape bounds).**

$$(\forall b, y,\ 0\leq q_{b}(y) \land \forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow 1-\sum_{a} \operatorname{captureProbability}\left(q, f, a\right) \leq \operatorname{escapeProbability}\left(q, f\right) \leq 1-\sum_{a} \operatorname{captureProbability}\left(q, f, a\right)+\sum_{a<a'} \operatorname{pairCaptureProbability}\left(q, f, a, a'\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni.escape_bonferroni_bounds` (`✓ std3`). ∎

*Citation.* Janos Galambos (1977). *Bonferroni Inequalities*. DOI: [10.1214/aop/1176995765](https://doi.org/10.1214/aop/1176995765).

*Commentary.*

The pointwise union and second-order Bonferroni inequalities are multiplied by nonnegative sample weights and summed.

The strict order writes each unordered pair exactly once.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni.escape_bonferroni_bounds`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteProductPairCapture](FiniteProductPairCapture.md)
