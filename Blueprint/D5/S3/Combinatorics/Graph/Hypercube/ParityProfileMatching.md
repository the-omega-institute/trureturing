# Optimal common-one counts in parity couplings

## Abstract

Integer couplings of the two parity classes have a sharp common-one count across coordinates.

**Theorem 1.1 (The greatest minimum common-one count).**

$$\forall n \in Nat,\; \forall k \in Nat,\; 0 < k \Rightarrow ((\exists w \in \operatorname{Couplings}\left(n, k\right),\; \forall i \in \operatorname{Coordinates}\left(n\right),\; \operatorname{Best}\left(n, k\right) \le \operatorname{CommonOne}\left(w, i\right)) \land (\forall w \in \operatorname{Couplings}\left(n, k\right),\; \exists i \in \operatorname{Coordinates}\left(n\right),\; \operatorname{CommonOne}\left(w, i\right) \le \operatorname{Best}\left(n, k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching.best_profile_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinates(n) is Fin(n+2). Couplings(n,k) consists of matrices of natural counts from the even profiles to the odd profiles with every row sum and every column sum equal to k. CommonOne(w,i) sums the entries whose two profiles both have bit one at i. With M = k times 2 to the power n, Best(n,k) is M minus the ceiling of M divided by n+2.

Each coordinate has M units of weight at bit one in each marginal. The total mismatch weight in that coordinate is twice the difference between M and its common-one count. Opposite parity forces at least one mismatch per weighted pair, so the sum of the differences across coordinates is at least M.

For attainment, distribute M units among the coordinates using the ceiling as a capacity and split the allocation into k batches of size 2 to the power n. Doubling the entries in each batch gives the even direction counts of a perfect matching by the Felzenbaum, Holzman and Kleitman criterion. The sum of the matching matrices realizes the bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching.best_profile_count`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube/DirectionMatching](DirectionMatching.md)
- Dependency: [D5/S3/Combinatorics/Transportation/OrderedMarginAllocation](../../Transportation/OrderedMarginAllocation.md)
