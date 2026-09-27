# Distance sets and equilateral point sets

## Abstract

Distance sets of finite point sets, and the three-point bound for equilateral sets in the Euclidean plane.

The distance set of a finite set of points collects the distances between distinct members, identifying repetitions. A finite point set has finitely many pairs in any metric space, so the definitions need no Euclidean or finite-dimensional hypothesis; the empty and one-point sets have no distances.

**Definition 1.1 (The distance set).**

Lean statement: `D5/S3/Geometry/Distances/DistanceSet.distanceSet`

*Formalization.* `D5/S3/Geometry/Distances/DistanceSet.distanceSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

distanceSet P is the set of real numbers realised as the distance between two distinct members of P.

**Definition 1.2 (The number of distinct distances).**

Lean statement: `D5/S3/Geometry/Distances/DistanceSet.distinctDistances`

*Formalization.* `D5/S3/Geometry/Distances/DistanceSet.distinctDistances` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

distinctDistances P is the cardinality of the distance set, obtained from the image of the finite set of pairs rather than from a convention for infinite sets.

**Theorem 1.3 (Equilateral sets in the plane have at most three points).**

Lean statement: `D5/S3/Geometry/Distances/DistanceSet.card_le_three_of_pairwise_dist_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Distances/DistanceSet.card_le_three_of_pairwise_dist_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite set of points in the Euclidean plane whose distinct members are all at one common distance has at most three elements. The bound is attained by an equilateral triangle.

## References

- Truth anchor: `D5/S3/Geometry/Distances/DistanceSet.card_le_three_of_pairwise_dist_eq`
- Truth anchor: `D5/S3/Geometry/Distances/DistanceSet.distanceSet`
- Truth anchor: `D5/S3/Geometry/Distances/DistanceSet.distinctDistances`
