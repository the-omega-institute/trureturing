# Boolean cube edge expansion

## Abstract

Every subset of a Boolean cube has at least its smaller side many crossing edges.

The two coordinate halves carry smaller cubes, joined by a perfect matching. Splitting a vertex set along this product gives a dimension induction for its edge boundary.

**Definition 1.1 (Recursive bit strings).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero-dimensional carrier is Unit. The successor carrier is Bool times the preceding carrier, so a vertex is a bit followed by its remaining coordinates.

**Definition 1.2 (Finite coordinate carrier).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.vertexFintype`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.vertexFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite enumeration is inherited recursively from Unit and the product with Bool.

**Definition 1.3 (Equality of bit strings).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.vertexDecidableEq`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.vertexDecidableEq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equality is decided recursively using equality of the leading Boolean coordinate and the tail.

**Definition 1.4 (Coordinate halves).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.slice`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.slice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The slice at a Boolean value consists of tails whose extension by that leading bit belongs to W. The two slice cardinalities sum to the cardinality of W.

**Definition 1.5 (Internal edges and the matching).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.edgeBoundary`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.edgeBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In dimension zero the recursive count is zero. In a successor dimension it is the sum of the two slice boundary counts and the cardinality of the symmetric difference of the slices. The latter counts exactly those matching edges whose endpoints have different membership in W.

**Definition 1.6 (One-coordinate adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.Adjacent`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.Adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two vertices are adjacent when either their leading bits agree and their tails are adjacent, or their leading bits differ and their tails agree. The zero-dimensional carrier has no adjacent pair. This is precisely the recursive Cartesian product description of the Boolean cube.

**Definition 1.7 (The cube as a simple graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.cubeGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.cubeGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjacency relation is symmetric and irreflexive, giving a simple graph on the recursive coordinate carrier.

**Definition 1.8 (Crossing edges counted once).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.boundaryEdges`

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.boundaryEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A boundary edge is an adjacent ordered pair with its first endpoint in W and its second endpoint outside W. Every undirected crossing edge has exactly one such orientation. The proof partitions this finite set into the boundaries inside the two halves and the crossing coordinate matching; the three sets are disjoint and each lifting map is injective. Consequently its cardinality equals the recursive boundary count.

**Theorem 1.9 (The edge expansion inequality).**

Lean statement: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.edge_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.edge_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural dimension n and every vertex set W, the number of crossing edges is at least the minimum of the cardinality of W and two to the power n minus that cardinality. No positivity, connectivity, or size restriction is imposed on W. The proof inducts on n. If the slices have sizes a and b in halves of size M, their internal boundaries contribute at least min(a,M-a) and min(b,M-b). The symmetric difference contributes enough to bound both a-b and b-a. These inequalities imply the required bound min(a+b,2M-a-b), including the empty and full sets and dimension zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.Adjacent`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.boundaryEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.cubeGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.edgeBoundary`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.edge_expansion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.slice`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.vertexDecidableEq`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/EdgeExpansion.vertexFintype`
