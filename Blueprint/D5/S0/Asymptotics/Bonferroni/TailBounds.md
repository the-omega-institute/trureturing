# Capture-Count Tail Bounds

## Abstract

Positive capture-count tails are bounded above and below by consecutive binomial moments.

**Theorem 1.1 (Tail mass decomposes by exact capture count).**

$$\operatorname{eventProbability}\left(q, k\leq N\right) = \sum_{{0\leq j\leq \lvert A \rvert}, k\leq j} \operatorname{eventProbability}\left(q, N = j\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/Bonferroni/TailBounds.capture_count_tail_eq_sum_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite capture count takes one value between zero and the address cardinality. Splitting the weighted sample sum at that value expresses the tail as the disjoint sum of its exact-count masses.

**Theorem 1.2 (The kth binomial moment bounds the kth tail from above).**

$$\operatorname{eventProbability}\left(q, k\leq N\right) \leq \sum_{T\subseteq A, \lvert T \rvert= k} \operatorname{setCaptureProbability}\left(q, f, T\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/Bonferroni/TailBounds.capture_count_tail_le_binomial_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every sample with at least k captures, choose(N,k) is at least one. Nonnegative sample weights preserve this pointwise inequality, and the exact binomial-moment identity converts the result to prescribed-set capture masses.

**Theorem 1.3 (Two consecutive moments bound the kth tail from below).**

$$\sum_{T\subseteq A, \lvert T \rvert= k} \operatorname{setCaptureProbability}\left(q, f, T\right) - k \cdot \sum_{T\subseteq A, \lvert T \rvert= k+1} \operatorname{setCaptureProbability}\left(q, f, T\right) \leq \operatorname{eventProbability}\left(q, k\leq N\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/Bonferroni/TailBounds.binomial_moment_sub_k_next_le_capture_count_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise, choose(N,k) minus k times choose(N,k+1) is at most the indicator of N at least k. The adjacent-binomial identity proves the inequality for all N, while nonnegative sample weights and the exact moment identity lift it to probabilities.

The coefficient k is minimal among constants uniform in the capture count: at N equal to k plus one, the pointwise left side is k plus one minus c, so a valid coefficient c must be at least k. The compiled small-cardinality tables in the Lean module validate the boundary cases.

## References

- Truth anchor: `D5/S0/Asymptotics/Bonferroni/TailBounds.binomial_moment_sub_k_next_le_capture_count_tail`
- Truth anchor: `D5/S0/Asymptotics/Bonferroni/TailBounds.capture_count_tail_eq_sum_exact`
- Truth anchor: `D5/S0/Asymptotics/Bonferroni/TailBounds.capture_count_tail_le_binomial_moment`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity](../WeightedProbability/BinomialMomentIdentity.md)
