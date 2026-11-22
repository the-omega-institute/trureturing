# Exact mismatch vectors for parity couplings

## Abstract

The even-word inequalities classify integer coordinate mismatch counts.

**Theorem 1.1 (Realizing prescribed coordinate disagreement counts).**

$$\forall n \in Nat,\; \forall k \in Nat,\; 0 < k \Rightarrow (\forall a \in \operatorname{CountVectors}\left(n\right),\; \operatorname{Realized}\left(n, k, a\right) \Leftrightarrow \operatorname{EvenCuts}\left(n, k, a\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/ParityMismatchCounts.exact_integer_parity_mismatch_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CountVectors(n) consists of natural-valued functions on Fin(n+2). Realized(n,k,a) means one natural count matrix between the even and odd profile classes has every row and column sum equal to k, with total coordinate disagreement count equal to twice a(i) at every i.

Let M be k times 2 to the power n. EvenCuts(n,k,a) means every a(i) is at most M and every even binary word e satisfies the following inequality. Sum a(i) over the zero coordinates of e and M minus a(i) over its one coordinates. The result is at least M.

For necessity, the two profiles in a used pair differ by an odd word, which has distance at least one from every even word. Summing the distances with the matrix weights gives the inequalities.

For sufficiency, fix the column sums of a binary table with twice M rows and minimize the number of even rows. Two distinct even rows allow a single-column swap that makes both odd. If an odd row differs from the common even row at more than one coordinate, one swap produces a different even row and reduces to that case. The only remaining positive minimum violates an even-word inequality. Apply Hall's prescribed-difference theorem to the odd rows using the product of the profile tail group and the cyclic group of copy indices. Summing the resulting labelled pairs over the copy indices gives the matrix.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/ParityMismatchCounts.exact_integer_parity_mismatch_counts`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube/DirectionMatching](DirectionMatching.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates](../../../QuantumBounds/MerminMeasurementDependence/Coordinates.md)
