# The Distinct Cycle Size Limit

## Abstract

The total weight of distinct cycle lengths over all permutations is asymptotic to n times n factorial.

**Definition 1.1 (Distinct lengths in a permutation).**

$$\forall n:\mathbb{N}, \forall \sigma:\operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin} n\right), \operatorname{DistinctCycleSizes}\left(\sigma\right)=\sigma.\operatorname{partition}.\operatorname{parts}.\operatorname{toFinset}$$

*Formalization.* `D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit.DistinctCycleSizes` (`✓ std3`).

*Citation.* Vaclav Kotesovec and Alois P. Heinz (2026). *OEIS A398726, distinct cycle size asymptotic conjecture*. URL: <https://oeis.org/A398726>.

*Commentary.*

The partition of a permutation records every cycle length, including one for each fixed point. Passing from its multiset of parts to a finite set retains each length once. Thus fixed points contribute length one when present, regardless of their multiplicity.

**Definition 1.2 (The sum over all permutations).**

$$\forall n:\mathbb{N}, \operatorname{CycleSizeSum}\left(n\right)=\sum_{\sigma:\operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin} n\right)} \sum_{k\in\operatorname{DistinctCycleSizes}\left(\sigma\right)} k$$

*Formalization.* `D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit.CycleSizeSum` (`✓ std3`).

*Citation.* Vaclav Kotesovec and Alois P. Heinz (2026). *OEIS A398726, distinct cycle size asymptotic conjecture*. URL: <https://oeis.org/A398726>.

*Commentary.*

For each permutation of Fin n, sum its distinct lengths and then sum over all permutations. This is the natural-valued statistic A398726. The empty permutation contributes zero; the statistic weights each distinct length by its size.

**Theorem 1.3 (Kotesovec's normalized limit).**

$$\operatorname{Filter}.\operatorname{Tendsto}\left(\left(n:\mathbb{N}\mapsto\frac{\left(\operatorname{CycleSizeSum}\left(n\right):\mathbb{R}\right)}{\left(n:\mathbb{R}\right)\cdot\left(\operatorname{Nat}.\operatorname{factorial}\left(n\right):\mathbb{R}\right)}\right),\operatorname{Filter}.\operatorname{atTop},\operatorname{nhds}\left(\left(1:\mathbb{R}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a398726-distinct-cycle-size-limit` (proved) by `D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a398726-distinct-cycle-size-limit","declaration_gid":"D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec and Alois P. Heinz (2026). *OEIS A398726, distinct cycle size asymptotic conjecture*. URL: <https://oeis.org/A398726>.

*Acknowledgement.* The Tau Ceti contributors (2026). *Conjugacy class sizes in the symmetric group*. URL: <https://github.com/TauCetiProject/TauCeti/blob/d7ac608e0c97f71e9e0dc210d26a470d974368d7/TauCeti/RepresentationTheory/Symmetric/ClassSize.lean>.

*Acknowledgement.* Philippe Flajolet and Robert Sedgewick (2009). *Analytic Combinatorics*. URL: <https://algo.inria.fr/flajolet/Publications/book.pdf>.

*Commentary.*

The real ratio of the complete statistic to n times n factorial tends to one along every sufficiently large natural index. The denominator is positive for n greater than zero; its zero-index value does not affect the limit.

Cauchy's class-size formula transfers the uniform permutation sum to partitions with weight one over the product of k to the power m_k times m_k factorial, where m_k is the multiplicity of part k. These weights sum to one, including the empty partition. The full-partition formulation adapts the cited TauCeti proof.

Removing two parts of length k injects partitions having at least two such parts into partitions of n minus twice k. The exact weight relation bounds the weighted second factorial moment by one over k squared. The average lost weight from repeated lengths is consequently nonnegative and at most the harmonic sum from one to n. Dividing by n gives a quantity tending to zero by the Cesaro theorem, which proves the stated limit.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit.CycleSizeSum`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit.DistinctCycleSizes`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit.result`
