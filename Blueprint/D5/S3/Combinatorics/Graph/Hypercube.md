# The Boolean hypercube and its edge count

## Abstract

The Boolean hypercube of dimension n is regular of degree n and therefore carries n times two to the power n minus one edges.

Vertices are the Boolean functions on a finite index type and adjacency is Hamming distance one, so the graph is the one-skeleton of the cube. Both facts below follow from that single adjacency condition, the second from the first by the degree-sum identity.

**Definition 1.1 (The hypercube graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube.hypercube`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube.hypercube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number n, hypercube n is the simple graph on the Boolean functions from the finite type of size n in which two vertices are adjacent exactly when their Hamming distance equals one. Symmetry comes from symmetry of Hamming distance and irreflexivity from the vanishing of the distance of a vertex to itself.

**Theorem 1.2 (Regularity of degree n).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube.hypercube_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube.hypercube_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vertex of hypercube n has exactly n neighbours. The proof exhibits a bijection from the index type to the neighbour set of a vertex x, sending an index i to the function that agrees with x away from i and negates x at i. That function is adjacent to x because the set of coordinates where the two disagree is the singleton on i. Injectivity follows by evaluating at the index, and surjectivity from the fact that a neighbour disagrees with x on a set of cardinality one, hence on a singleton, and a Boolean value differing from x at that coordinate is its negation.

**Theorem 1.3 (The edge count).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube.hypercube_edge_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube.hypercube_edge_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of edges of hypercube n is n times two to the power n minus one, where the exponent uses truncated subtraction of naturals. Summing the degrees gives twice the edge count; regularity turns the sum into n times the number of vertices, which is n times two to the power n. Dividing by two gives the claim for positive n, and for n equal to zero both sides vanish, so the truncated exponent causes no exception.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube.hypercube`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube.hypercube_edge_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube.hypercube_regular`
