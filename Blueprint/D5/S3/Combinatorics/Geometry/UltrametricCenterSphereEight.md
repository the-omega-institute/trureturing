# An eight-point model with two prescribed gap distances

## Abstract

For every two prescribed distances strictly between zero and one, an eight-point ultrametric has the exact distance center and sphere counts required for sharpness.

Throughout, u and v are arbitrary real numbers satisfying $0 < u < v < 1$. Write E for Eight u v hu huv hv, with the metric and ultrametric instances inherited from the constant cross-distance join. Every statement below holds for every such pair, and every point p is arbitrary in E.

**Remark 1.1 (The nested join construction).**

Lean statement: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.Eight`

*Formalization.* `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.Eight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Pair joins two singleton spaces at its weight. A Block joins two such pairs at distance one. Eight joins two blocks at distance two; the first block uses weight u and the second uses weight v. Thus the two prescribed gap distances are kept separate between the blocks.

The component order calculations are `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.pair_card` and `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.block_card`. Their strict bounds are `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.pair_dist_lt_one` and `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.block_dist_lt_two`.

**Theorem 1.2 (The carrier has eight points).**

$$\operatorname{card}\left(E\right) = 8$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order follows by summing two four-point blocks, each consisting of two two-point pairs.

**Theorem 1.3 (Every zero sphere has one point).**

$$\operatorname{card}\left(\operatorname{sphere}\left(p, 0\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_zero_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero sphere is the singleton consisting of its center, by identity of indiscernibles.

**Theorem 1.4 (Every sphere at one has two points).**

$$\operatorname{card}\left(\operatorname{sphere}\left(p, 1\right)\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_one_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At distance one, p sees exactly the other pair in its own block. Its own pair lies strictly below one; the other block lies at distance two.

**Theorem 1.5 (Every sphere at two has four points).**

$$\operatorname{card}\left(\operatorname{sphere}\left(p, 2\right)\right) = 4$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_two_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At distance two, p sees exactly the four points of the other block. All distances within its own block are strictly below two.

**Theorem 1.6 (The original distance center is exactly zero, one and two).**

$$\operatorname{center}\left(E\right) = \{0,1,2\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The center is the project's distance-center predicate, with nonnegative radii and a witness at every point. The three prescribed radii are central by their pointwise sphere counts. A gap distance from one block is absent at every point in the other block; distinctness of u and v excludes an additional central radius.

**Theorem 1.7 (The construction introduces no other distances).**

$$\operatorname{dist}\left(p, q\right) \in \{0,u,v,1,2\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.distance_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every p and q in E, the distance lies in the displayed set. In particular no distance strictly between one and two is introduced. Exact occurrence of both prescribed gap values is established in the sharpness module by eight_exact_distance_values.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.Eight`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.block_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.block_dist_lt_two`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.distance_values`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_center`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.pair_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.pair_dist_lt_one`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_one_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_two_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_zero_card`
- Dependency: [D5/S3/Combinatorics/Geometry/UltrametricConstantJoin](UltrametricConstantJoin.md)
