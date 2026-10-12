# Standard small cubic graph forms

## Abstract

Isomorphism forms for cubic graphs on four and six vertices.

**Definition 1.1 (The four-vertex model).**

$$modelFour = \operatorname{CompleteGraph}\left(\operatorname{Fin}\left(4\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.modelFour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The modelFour graph is the complete simple graph on Fin 4.

**Definition 1.2 (The complement of two triangles).**

$$\operatorname{CompleteBipartite}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.modelSixTriangles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph modelSixTriangles has vertex type Fin 6. Two vertices are adjacent precisely when one has value less than three and the other has value at least three.

**Definition 1.3 (The complement of a six-cycle).**

$$modelSixCycle = \operatorname{Complement}\left(\operatorname{CycleGraph}\left(6\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.modelSixCycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph modelSixCycle is the complement of Mathlib's cycleGraph 6, whose cycle follows the vertex order 0,1,2,3,4,5.

**Theorem 1.4 (The four-vertex isomorphism).**

$$\operatorname{Cubic}\left(G\right) \land \operatorname{VertexCount}\left(G\right) = 4 \implies \operatorname{Isomorphic}\left(G, modelFour\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.cubic_four_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every simple cubic graph on a finite vertex type of cardinality four is isomorphic to modelFour. Cardinality supplies a vertex equivalence and the degree condition makes adjacency equivalent to vertex inequality.

**Theorem 1.5 (The six-vertex isomorphism alternatives).**

$$\operatorname{Cubic}\left(G\right) \land \operatorname{VertexCount}\left(G\right) = 6 \implies \operatorname{Isomorphic}\left(G, modelSixTriangles\right) \lor \operatorname{Isomorphic}\left(G, modelSixCycle\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.cubic_six_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every simple cubic graph on a finite vertex type of cardinality six is isomorphic either to modelSixTriangles or to modelSixCycle. Its complement has degree two. A structural vertex listing identifies that complement with two disjoint triangles or a six-cycle, and the same equivalence identifies the original graph with the corresponding complement model.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.cubic_four_iso`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.cubic_six_iso`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.modelFour`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.modelSixCycle`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso.modelSixTriangles`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall](CubicARGraphSmall.md)
