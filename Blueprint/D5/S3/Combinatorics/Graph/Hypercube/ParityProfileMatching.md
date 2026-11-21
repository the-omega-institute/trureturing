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

**Theorem 1.2 (A boundary vector dominates each feasible floor).**

$$\forall n \in Nat,\; \forall k \in Nat,\; \forall v \in \operatorname{CountVectors}\left(n\right),\; \operatorname{FeasibleFloor}\left(n, k, v\right) \Rightarrow (\exists u \in \operatorname{CountVectors}\left(n\right),\; \operatorname{Boundary}\left(n, k, u\right) \land (\forall i \in \operatorname{Coordinates}\left(n\right),\; \operatorname{Value}\left(v, i\right) \le \operatorname{Value}\left(u, i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching.profile_floor_dominated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CountVectors(n) consists of natural-valued functions on Coordinates(n), and Value(v,i) is the value of v at coordinate i. FeasibleFloor(n,k,v) means one coupling in Couplings(n,k) has common-one counts at least v at every coordinate. Boundary(n,k,u) means that u(i) is at most M at every coordinate and the sum of M minus u(i) equals M. Allocate the M units of deficit below the coordinate capacities M minus v(i).

**Theorem 1.3 (The maximal common-one count vectors).**

$$\forall n \in Nat,\; \forall k \in Nat,\; \forall v \in \operatorname{CountVectors}\left(n\right),\; (\operatorname{FeasibleFloor}\left(n, k, v\right) \land (\forall u \in \operatorname{CountVectors}\left(n\right),\; (\operatorname{FeasibleFloor}\left(n, k, u\right) \land (\forall i \in \operatorname{Coordinates}\left(n\right),\; \operatorname{Value}\left(v, i\right) \le \operatorname{Value}\left(u, i\right))) \Rightarrow u = v)) \Leftrightarrow \operatorname{Boundary}\left(n, k, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching.exact_profile_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prescribed-direction matchings realize every boundary vector. Strict coordinatewise improvement over such a vector would force the total deficit below M.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching.best_profile_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching.exact_profile_frontier`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching.profile_floor_dominated`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube/DirectionMatching](DirectionMatching.md)
- Dependency: [D5/S3/Combinatorics/Transportation/OrderedMarginAllocation](../../Transportation/OrderedMarginAllocation.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates](../../../QuantumBounds/MerminMeasurementDependence/Coordinates.md)
