# Finite simplicial join realization

## Abstract

The ordinary quotient join and the finite coordinate simplicial join realization.

**Definition 1.1 (The endpoint equivalence relation).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialJoin.ordinaryJoinSetoid`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialJoin.ordinaryJoinSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Representatives are triples (x,y,t) in the actual product of the two spaces and the closed unit interval. They are equivalent exactly when their parameters agree, their left coordinates agree unless t is one, and their right coordinates agree unless t is zero. Interior representatives retain both coordinates.

**Definition 1.2 (The ordinary topological join).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialJoin.OrdinaryJoin`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialJoin.OrdinaryJoin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary join is the quotient by the endpoint equivalence relation, with the native quotient topology of the product topology. If either factor is empty this ordinary join is empty.

**Definition 1.3 (Nonempty tagged faces).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialJoin.simplicialJoin`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialJoin.simplicialJoin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For complexes M on V and N on W, a face of their join is a nonempty finite subset of V disjoint union W. Each nonempty tagged block must be a face of its corresponding complex. Either block may be empty; the whole face may not. Downward closure is proved for every nonempty subface.

**Definition 1.4 (The actual coordinate realization).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialJoin.Space`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialJoin.Space` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor and target spaces use FiniteConeCollapse.realization: the union of the convex hulls of coordinate vertices of actual faces, with the ambient real coordinate subspace topology. Both vertex types are finite.

**Definition 1.5 (Barycentric coordinates).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialJoin.representative`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialJoin.representative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left coordinate at v is (1-t) times x(v), and the right coordinate at w is t times y(w). Nonnegativity, total mass one and support in the disjoint sum of actual factor faces put the image in the actual join realization.

**Theorem 1.6 (Exact quotient fibers).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialJoin.representative_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplicialJoin.representative_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two barycentric vectors are equal if and only if their representatives are endpoint equivalent. Summing the right coordinates recovers t. Cancellation recovers the left point when t is not one and the right point when t is not zero. At an endpoint the other block vanishes exactly as required by the ordinary join relation.

**Definition 1.7 (The continuous quotient map).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialJoin.realizationMap`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialJoin.realizationMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The barycentric map is continuous coordinate by coordinate and constant exactly on the endpoint equivalence classes, so its native quotient lift is continuous.

**Definition 1.8 (Homeomorphism of actual realizations).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialJoin.joinHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteSimplicialJoin.joinHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair of finite vertex types and pre-abstract simplicial complexes M and N with both actual factor realizations nonempty, their ordinary topological join is homeomorphic to the actual coordinate realization of their simplicial join. For surjectivity, sum the target's right block to obtain t and normalize each positive-mass block inside its actual factor face. For a zero-mass block, use a chosen actual point in that nonempty factor. Each factor realization is a finite union of compact convex hulls. The source quotient is therefore compact and the target is Hausdorff, so the continuous bijection is a homeomorphism. This classical bridge does not establish graph substitution, sphere-join identities, finite sphere-wedge closure or the full Question 22 of Carnero Bravo. The nonempty hypotheses exclude the ordinary-join versus augmented-empty-face convention mismatch.

**Theorem 1.9 (The representative formula).**

Lean statement: `D5/S3/Geometry/FiniteSimplicialJoin.joinHomeomorph_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSimplicialJoin.joinHomeomorph_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all actual points x and y and all interval parameters t, the homeomorphism sends the class of (x,y,t) to the vector with left block (1-t)x and right block ty, including both endpoints.

## References

- Truth anchor: `D5/S3/Geometry/FiniteSimplicialJoin.OrdinaryJoin`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialJoin.Space`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialJoin.joinHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialJoin.joinHomeomorph_apply`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialJoin.ordinaryJoinSetoid`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialJoin.realizationMap`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialJoin.representative`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialJoin.representative_eq_iff`
- Truth anchor: `D5/S3/Geometry/FiniteSimplicialJoin.simplicialJoin`
- Dependency: [D5/S3/Geometry/FiniteConeCollapse](FiniteConeCollapse.md)
