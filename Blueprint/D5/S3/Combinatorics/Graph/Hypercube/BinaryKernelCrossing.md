# Crossing pairs in the binary cube adjacency kernel

## Abstract

Crossing pairs in the binary cube adjacency kernel

A cube vertex is the subset of coordinates with bit one. For a pivot x, the symmetric difference with x records the changed coordinates and its cardinality is Hamming distance. This lets x serve as the origin for any pivot. Each coordinate flip gives a distinct neighbor, so the mod-two adjacency equation says that the number of selected directions is even.

**Definition 1.1 (Selected neighbor directions).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.neighborDirections`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.neighborDirections` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite cube support R and a vertex x, retain the coordinate directions whose singleton flip of x lies in R.

**Theorem 1.2 (Distance-three and total support bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.crossing_pair_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.crossing_pair_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k count selected neighbors of a pivot x and suppose every vertex two flips from x has an even number of neighbors in R. Each pair consisting of a selected direction i and an unselected direction j determines a two-flip vertex. Exactly one of its neighbors that undo either flip is selected. Even degree requires another selected neighbor, reached by flipping a third coordinate.

The three changed coordinates split into selected and unselected directions at x. The product of the two part sizes is at most two, so each distance-three support vertex covers at most two crossing pairs. The k(n − k) crossing pairs give the distance-three bound. The k distinct distance-one vertices are disjoint from that layer and give the total bound 2|R| ≥ 2k + k(n − k).

In the 10+4 rook case for an 84-vertex component in the nine-cube, the 24 forced singleton contacts form a binary kernel support in the folded eight-cube. This leaves eight further singleton sites. If the extra even dimer meets four of them, the bound requires at least eight sites at distance three and twelve in total. This excludes that rook case in the study of Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Theorem 1.3 (The weight of a nonzero kernel word).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.card_ge_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.card_ge_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In positive dimension, choose a pivot next to a support vertex. Its selected degree is positive and even, hence at least two. Since k ≤ n, the crossing bound is at least 2k + 2(n − k) = 2n. In dimension zero the claimed lower bound is zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.card_ge_dimension`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.crossing_pair_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelCrossing.neighborDirections`
