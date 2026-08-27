# Observation Rank Monotonicity

## Abstract

Observation-subspace rank is monotone under inclusion.

**Theorem 1.1 (Adding observation settings cannot decrease rank).**

$$\begin{aligned}\forall K, V, I: \operatorname{Type},\\{}[\operatorname{DivisionRing}(K)], [\operatorname{AddCommGroup}(V)], [\operatorname{Module}(K, V)],\\{}[\operatorname{FiniteDimensional}(K, V)],\\\forall U: I \to \operatorname{Submodule}(K, V), A, B: \operatorname{Set}(I),\\A \subseteq B \Rightarrow \operatorname{finrank}(K, \operatorname{iSupOnSubtype}(A, U)) \leq \operatorname{finrank}(K, \operatorname{iSupOnSubtype}(B, U)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ObservationRankMonotonicity.observation_rank_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each setting contributes a subspace. Inclusion of selected index sets induces inclusion between their indexed subspace suprema, and finite-dimensional rank is monotone along that inclusion.

## References

- Truth anchor: `D5/S3/Observer/Linear/ObservationRankMonotonicity.observation_rank_monotonicity`
- Dependency: [D5/S3/Observer/Linear/ObservationRankSubmodularity](ObservationRankSubmodularity.md)
