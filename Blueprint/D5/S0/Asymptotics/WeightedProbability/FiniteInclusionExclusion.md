# Finite Capture Inclusion-Exclusion

## Abstract

Finite weighted capture is exactly the alternating sum of all nonempty intersection events.

**Theorem 1.1 (Exact weighted capture inclusion-exclusion).**

$$\operatorname{eventProbability}\left(q, \{s \mid \exists a,\ \operatorname{Captured}\left(f, s, a\right)\}\right) = \sum_{\emptyset\neq T \subseteq A}(-1)^{\lvert T \rvert+1} \operatorname{eventProbability}\left(q, \{s \mid \forall a\in T,\ \operatorname{Captured}\left(f, s, a\right)\}\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion.capture_event_inclusion_exclusion` (`✓ std3`). ∎

*Citation.* Gerald Berman and K. D. Fryer (1972). *The Inclusion-Exclusion Principle*. DOI: [10.1016/b978-0-12-092750-0.50008-9](https://doi.org/10.1016/b978-0-12-092750-0.50008-9).

*Commentary.*

Mathlib's pointwise finite-union indicator identity is applied directly to the captured-address events and then summed against sampleWeight.

The identity is linear, so it requires neither nonnegative weights nor normalized marginals.

**Theorem 1.2 (The first two truncations are the frozen escape sandwich).**

$$(\forall b, y,\ 0\leq q_{b}(y) \land \forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow 1-\sum_{T\subseteq A, \lvert T \rvert=1}\operatorname{eventProbability}\left(q, \{s \mid \forall a\in T,\ \operatorname{Captured}\left(f, s, a\right)\}\right) \leq \operatorname{escapeProbability}\left(q, f\right) \leq 1-\sum_{T\subseteq A, \lvert T \rvert=1}\operatorname{eventProbability}\left(q, \{s \mid \forall a\in T,\ \operatorname{Captured}\left(f, s, a\right)\}\right)+\sum_{T\subseteq A, \lvert T \rvert=2}\operatorname{eventProbability}\left(q, \{s \mid \forall a\in T,\ \operatorname{Captured}\left(f, s, a\right)\}\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion.escape_bonferroni_truncations_of_inclusion_exclusion` (`✓ std3`). ∎

*Citation.* Janos Galambos (1977). *Bonferroni Inequalities*. DOI: [10.1214/aop/1176995765](https://doi.org/10.1214/aop/1176995765).

*Commentary.*

The degree-one subset sum is proved equal to the frozen captureProbability sum.

A bijection from strictly ordered pairs to two-element subsets proves that the degree-two subset sum is the frozen pairProbabilitySum. Rewriting by those two public lemmas reduces the result exactly to the imported frozen escape_bonferroni_bounds theorem.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion.capture_event_inclusion_exclusion`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion.escape_bonferroni_truncations_of_inclusion_exclusion`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni](FiniteBonferroni.md)
