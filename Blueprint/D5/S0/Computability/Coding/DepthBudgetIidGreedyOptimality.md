# Greedy Prefix Codes with Arbitrary Depth Budgets

## Abstract

One iid greedy prefix code maximizes every finite truncation and the total mass.

Let A be a finite alphabet, p a strictly positive real probability vector on A, and b an arbitrary natural-valued function on depths. A word has mass equal to the product of p over its letters. At each depth fix a total tie order on words. Priority first compares iid word mass in decreasing order and then the fixed tie order. No computability assumption is imposed on p.

Start with the empty word as the live frontier. Extend every live word by every letter, select the first min(b(n), live count) words in priority order at the positive depth n, and continue from the remaining frontier. The union G of all selected words is defined by this single recursion, without a terminal depth. Thus o(n) = priority(p,tie(n)) and G = greedyCode(o,b).

Legal(b,F) means that F is prefix-free, excludes the empty word and contains at most b(n) distinct words of each length n. Write T(p,F,N) for the sum of iid masses of words of F of length at most N, and S(p,F) for the nonnegative countable sum over all words of F. The latter is represented in the extended nonnegative reals. IsGreatest asserts membership and an upper bound for every member of the displayed set. The condition depthAtMost(F,N) means that every word of F has length at most N.

**Theorem 1.1 (One code attains all finite maxima and the infinite supremum).**

$$\forall p, b, tie, (\forall a, 0 < \operatorname{p}\left(a\right)) \land \sum_a \operatorname{p}\left(a\right) = 1 \Rightarrow \operatorname{Legal}\left(b, G\right) \land (\forall N, \operatorname{IsGreatest}\left(\{x \mid \exists F, \operatorname{Legal}\left(b, F\right) \land \operatorname{depthAtMost}\left(F, N\right) \land x = \operatorname{T}\left(p, F, N\right)\}, \operatorname{T}\left(p, G, N\right)\right)) \land \operatorname{IsGreatest}\left(\{x \mid \exists F, \operatorname{Legal}\left(b, F\right) \land x = \operatorname{S}\left(p, F\right)\}, \operatorname{S}\left(p, G\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each mass threshold, the greedy live frontier has no more words above that threshold than any competitor. Iid expansion preserves this comparison by summing over letters. Removing the heaviest permitted words preserves it under any competing deletion within the same budget.

Hall's marriage theorem converts threshold domination into an injective matching with no smaller masses on the competitor side. Conservation of live mass plus deleted mass gives finite optimality. Prefix freedom identifies the recursive competitor frontier with the words having no selected ancestor. Suprema of nonnegative finite sums give the infinite conclusion for the same G.

Depth zero, zero budgets, skipped depths, saturation and permanently empty frontiers are included. No summable budget tail, compactness or continuity of the objective is required. The result also allows a singleton alphabet; in particular it applies when A has at least two letters.

## References

- Truth anchor: `D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality`
- Dependency: [D5/S0/Computability/Coding/PrefixFreeCode](PrefixFreeCode.md)
