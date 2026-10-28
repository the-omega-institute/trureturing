# Finite cone union wedge

## Abstract

The actual quotient wedge for a finite union along a nonempty cone.

**Definition 1.1 (Subset collapse relation).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.subsetSetoid`

*Formalization.* `D5/S3/Geometry/FiniteConeUnionWedge.subsetSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any subset C of a space, two points are related exactly when they are equal or both belong to C.

**Definition 1.2 (Two distinguished points).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.wedgePoints`

*Formalization.* `D5/S3/Geometry/FiniteConeUnionWedge.wedgePoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For points a of X and b of Y, the distinguished subset of the disjoint sum consists exactly of inl a and inr b. The wedge is its collapse quotient with the quotient topology.

**Definition 1.3 (A closed cover with controlled overlap).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.CollapseCover`

*Formalization.* `D5/S3/Geometry/FiniteConeUnionWedge.CollapseCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two continuous injective closed maps from X and Y cover Z. Every equality between points from opposite summands lies in the subset C, and both chosen basepoints map into C. These are map and subset conditions; no gluing continuity, homotopy extension property, or equivalence is assumed.

**Definition 1.4 (The actual quotient homeomorphism).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.quotientWedgeHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteConeUnionWedge.quotientWedgeHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The wedge of the actual quotients of X and Y by the preimages of C is homeomorphic to Z modulo C. The map from the disjoint sum to Z is a continuous closed surjection, hence a quotient map. After descending on both arms, the resulting quotient map has exactly the two-basepoint wedge relation as kernel. The homeomorphism is obtained from that kernel equality. The proof includes the degenerate cases in which C is a whole summand or the whole space.

**Theorem 1.5 (Actual intersections of finite realizations).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.realization_intersection`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeUnionWedge.realization_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type V and every pair M,N of pre-abstract simplicial complexes on V, the coordinate realization of M intersect N equals the intersection of their coordinate realizations. A point represented in faces s and t belongs to the simplex of s intersect t; the coordinate sum one proves that this common face is nonempty. Downward closure then places it in both complexes. No empty face is assumed to be a face.

**Definition 1.6 (Concrete finite cone union data).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.ConeUnion`

*Formalization.* `D5/S3/Geometry/FiniteConeUnionWedge.ConeUnion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data are two finite-vertex complexes, their intersection cone, and an apex. The singleton apex is a cone face, and adjoining the apex preserves cone faces. The intersection equality is an equality of complexes, rather than an assumed topological intersection statement.

**Definition 1.7 (The left cone pair).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.leftPair`

*Formalization.* `D5/S3/Geometry/FiniteConeUnionWedge.leftPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left native coordinate realization contains the specified cone and has its coordinate apex as basepoint.

**Definition 1.8 (The right cone pair).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.rightPair`

*Formalization.* `D5/S3/Geometry/FiniteConeUnionWedge.rightPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The right native coordinate realization contains the same cone and has the same coordinate apex as basepoint.

**Definition 1.9 (The union cone pair).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.unionPair`

*Formalization.* `D5/S3/Geometry/FiniteConeUnionWedge.unionPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient complex is the actual union of the two face collections. The specified intersection cone is a subcomplex of that union.

**Definition 1.10 (The cone-union wedge equivalence).**

Lean statement: `D5/S3/Geometry/FiniteConeUnionWedge.homotopyEquiv`

*Formalization.* `D5/S3/Geometry/FiniteConeUnionWedge.homotopyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every ConeUnion, the actual coordinate realization of the union is homotopy equivalent to the quotient wedge of the two native coordinate realizations at their common apex. Each realization is closed because it is a finite union of closed convex hulls. The proved realization intersection identity establishes the exact overlap. Compose the existing explicit finite cone collapse of the union, the actual quotient homeomorphism, and the inverse of the wedge map induced by the two local cone collapses. Both local inverse homotopies are relative to the apex or its quotient class. Their disjoint-sum homotopies descend jointly continuously to the wedge by the quotient-product lifting theorem, using local compactness of the unit interval. This is the classical cone-union topology used in the single-vertex substitution route of Carnero Bravo, arXiv:2505.06457v2, Question 22. It asserts neither a solution of that question nor novelty; the graph, join, hereditary induction and sphere-model obligations remain outside this theorem.

## References

- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.CollapseCover`
- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.ConeUnion`
- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.homotopyEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.leftPair`
- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.quotientWedgeHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.realization_intersection`
- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.rightPair`
- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.subsetSetoid`
- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.unionPair`
- Truth anchor: `D5/S3/Geometry/FiniteConeUnionWedge.wedgePoints`
- Dependency: [D5/S3/Geometry/FiniteConeCollapse](FiniteConeCollapse.md)
