# Three-Tower Cost Separation

## Abstract

Fixed-overhead compilers squeeze three affordable regions, while spikes and range tables witness two strict exponential cost gaps.

**Theorem 1.1 (Compiler inclusions give a distance sandwich and two strict separations).**

$$\begin{gathered}\forall P, T, K, cPT, cTK, x, B,\\{}\operatorname{CostCompiler}\left(P, T, cPT\right) \land \operatorname{CostCompiler}\left(T, K, cTK\right) \land \operatorname{Nonempty}\left(\operatorname{Affordable}\left(P, B\right)\right) \Rightarrow \\{}(\operatorname{infDist}\left(x, \operatorname{Affordable}\left(K, B + cPT + cTK\right)\right) \leq \operatorname{infDist}\left(x, \operatorname{Affordable}\left(T, B + cPT\right)\right) \land \operatorname{infDist}\left(x, \operatorname{Affordable}\left(T, B + cPT\right)\right) \leq \operatorname{infDist}\left(x, \operatorname{Affordable}\left(P, B\right)\right)) \land \\{}(\forall j\in\mathbb{N}, \operatorname{indexedSpikeValue}\left(\operatorname{pow}\left(2, j\right)\right) = \operatorname{spike}\left(\operatorname{pow}\left(2, j\right)\right) \land \operatorname{indexedSpikeCost}\left(\operatorname{pow}\left(2, j\right)\right) = j + 1 \land \operatorname{indexedSpikeCost}\left(\operatorname{pow}\left(2, j\right)\right) < \operatorname{pow}\left(2, j\right) + 1 \land (\forall bits, \operatorname{prefixValue}\left(bits\right) = \operatorname{spike}\left(\operatorname{pow}\left(2, j\right)\right) \Rightarrow \operatorname{pow}\left(2, j\right) + 1 \leq \operatorname{length}\left(bits\right))) \land \\{}(\forall j\in\mathbb{N}, j \ge 2 \Rightarrow \operatorname{explicitTableValue}\left(\operatorname{range}\left(\operatorname{pow}\left(2, j\right)\right)\right) = \operatorname{rangeProgramValue}\left(\operatorname{pow}\left(2, j\right)\right) \land \operatorname{explicitTableCost}\left(\operatorname{range}\left(\operatorname{pow}\left(2, j\right)\right)\right) = \operatorname{pow}\left(2, j\right) \land \operatorname{rangeProgramCost}\left(\operatorname{pow}\left(2, j\right)\right) = j + 1 \land \operatorname{rangeProgramCost}\left(\operatorname{pow}\left(2, j\right)\right) < \operatorname{explicitTableCost}\left(\operatorname{range}\left(\operatorname{pow}\left(2, j\right)\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/ThreeTowerCostSeparation.three_tower_cost_sandwich_and_double_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A semantics-preserving prefix-to-test compiler with overhead c_PT and a test-to-program compiler with overhead c_TK embed the affordable regions at budgets B, B+c_PT, and B+c_PT+c_TK. The frozen nested-set distance theorem then reverses these inclusions into the stated infimum-distance sandwich.

The nonemptiness premise on the prefix region is essential: real-valued infDist totalizes the empty-set case to zero. The source's unspecified additive constants are also made explicit as natural overheads and are accumulated in the two shifted budgets.

For the first strict family, the spike at coordinate 2^j has indexed cost j+1, while every literal Boolean prefix denoting it has length at least 2^j+1. For the second, the literal table range(2^j) has cost 2^j, while the program that computes the same range has cost j+1; this gap is strict for j at least two.

Pinned Mathlib supplies List.getD_eq_default, Nat.log_pow, Nat.lt_two_pow_self, and Finset.card_range. The repository search found and directly reuses NameSetDistanceSandwich for the metric consequence; keyword, symbol-variant, digestion-state, generalized, and in-flight searches found neither strict separation family.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/ThreeTowerCostSeparation.three_tower_cost_sandwich_and_double_separation`
- Dependency: [D5/S0/Asymptotics/NameSetDistanceSandwich](../../Asymptotics/NameSetDistanceSandwich.md)
