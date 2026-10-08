# Relabeling a Word Tree

## Abstract

History-dependent relabeling preserves prefix codes and their mass.

At each original history h choose a permutation pi(h) of the alphabet. Relabel the next letter using that permutation and continue in the original history. The inverse decodes a letter before extending the recovered history. These recursions are inverse bijections on words. They preserve lengths and the prefix relation in both directions.

Let q(h,a) = p(pi(h)(a)). The conditional mass of a word is the product of the rows encountered along its actual path. Its relabeled iid mass is the same product. Legal(b,F) uses the canonical prefix-free code condition, excludes the empty word and bounds the number of different words at each depth by b.

**Theorem 1.1 (Transport of codes, budgets and mass).**

$$\forall pi, p, q, b, F, (\forall h, a, \operatorname{q}\left(h, a\right) = \operatorname{p}\left(\operatorname{pi}\left(h, a\right)\right)) \land \operatorname{Legal}\left(b, F\right) \Rightarrow \operatorname{Legal}\left(b, \operatorname{phi}\left(F\right)\right) \land (\forall N, \operatorname{T}\left(q, F, N\right) = \operatorname{T}\left(p, \operatorname{phi}\left(F\right), N\right)) \land \operatorname{S}\left(q, F\right) = \operatorname{S}\left(p, \operatorname{phi}\left(F\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/HistoryTreeRelabeling.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The level sets are bijective images, so their cardinalities and finite sums are preserved. Reindexing the nonnegative countable sum by the same bijection gives the total-mass identity. No independence or finite-memory condition is imposed on q; the row identity is the required hypothesis.

## References

- Truth anchor: `D5/S0/Computability/Coding/HistoryTreeRelabeling.result`
- Dependency: [D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality](DepthBudgetIidGreedyOptimality.md)
