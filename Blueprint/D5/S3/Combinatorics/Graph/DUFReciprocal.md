# Local graphs and reciprocal double counting

## Abstract

Reciprocal incidence weights connect the local three-colored graphs of a finite triple family with its occupied pairs and nonempty common links. All vertex types are arbitrary finite types; there is no bound on degrees or class sizes.

**Definition 1.1 (Reciprocal incidence weight).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFReciprocal.weight`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFReciprocal.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each coordinate a of e, the first sum uses the reciprocal of the number of extensions of e with a erased. The second sum runs over every distinct replacement x and uses one half the reciprocal size of K({a,x}). The values are rational.

**Definition 1.2 (Actual local vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFReciprocal.localVertices`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFReciprocal.localVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A local vertex consists of a coordinate a of e and a vertex x outside e such that replacing a by x gives a member of H. Its color is a.

**Definition 1.3 (Actual local adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFReciprocal.adjacent`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFReciprocal.adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two local vertices (a,x) and (b,y) are adjacent exactly when a and b differ, x and y differ, and the set consisting of x, y, and the coordinate of e remaining after a and b are erased belongs to H. On a triple this is a symmetric irreflexive relation and adjacent vertices have different colors.

**Definition 1.4 (Actual local neighborhoods).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFReciprocal.localNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFReciprocal.localNeighbors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The neighborhood filters the actual local vertex set by the adjacency relation.

**Theorem 1.5 (Common-link correspondence and mixed degree).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFReciprocal.local_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFReciprocal.local_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume H has unique unordered disjoint unions and e is a member of H with three vertices. For every local vertex (a,x), its degree plus one equals the size of K({a,x}). If two local neighbors have distinct colors, its degree is exactly two. The base pair e with a erased is a common-link member. Every other common-link pair intersects this base pair in exactly one vertex and corresponds to exactly one local neighbor. The two possible intersection vertices give the two neighbor colors. If both colors occur, pairwise intersection forces their external values to coincide and each of the two color classes in this neighborhood to be a singleton.

**Theorem 1.6 (Unrestricted three-uniform DUF bound).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFReciprocal.reciprocal_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFReciprocal.reciprocal_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite ground type with n vertices and every finite family H of three-element sets having unique unordered disjoint unions, 23 times the size of H is at most 24 times the number of ground pairs. The actual local graph of each triple has the required proper three-coloring and mixed degree two. Its potential equals the incidence weight: a color class has one fewer member than its opposite-pair extension set, and the degree correspondence identifies the other denominators. Summing these weights counts each occupied pair once and each nonempty common link once. The first multiplicity is the extension-set size; the second is twice the common-link size and cancels the factor one half. Each of these two sets of ground pairs has size at most n choose two. Combining this exact double count with the local bound 23/12 gives the stated inequality. This is an auxiliary coefficient bound for three-uniform families; it does not give coefficient one or settle the general Erdős problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DUFReciprocal.adjacent`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFReciprocal.localNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFReciprocal.localVertices`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFReciprocal.local_correspondence`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFReciprocal.reciprocal_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFReciprocal.weight`
- Dependency: [D5/S3/Combinatorics/Graph/DUFStructure](DUFStructure.md)
- Dependency: [D5/S3/Combinatorics/Graph/ThreeColorReciprocal](ThreeColorReciprocal.md)
