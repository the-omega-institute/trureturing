# Two lower-gap distances are necessary and sufficient

## Abstract

The pointwise counts one, two and four at central radii zero, one and two force order eight and two distinct lower-gap distances; every prescribed pair attains the bound without an upper-gap distance.

**Theorem 1.1 (Every realization has order eight and two distinct distances below one).**

$$\operatorname{card}\left(X\right) = 8 \land \exists p,q,r,s:X, 0 < \operatorname{dist}\left(p, q\right) < 1 \land 0 < \operatorname{dist}\left(r, s\right) < 1 \land \operatorname{dist}\left(p, q\right) \neq \operatorname{dist}\left(r, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereSharpness.order_eight_and_two_gap_distances` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be an arbitrary finite nonempty metric space with IsUltrametricDist. Assume its original distance center is exactly the real set consisting of zero, one and two, and assume every sphere at one has two points and every sphere at two has four points. Then the displayed conjunction holds. The zero sphere automatically has one point. No distance-support restriction or preselected gap pair is assumed in this lower bound.

The recurrence forces order eight. Partitioning the strict ball at two into closed balls at one forces each point to have a neighbor at a distance strictly between zero and one. A single such distance common to all points would be central; the center equality rules this out and yields two distinct gap distances.

**Theorem 1.2 (Every prescribed lower-gap pair gives exactly the five distance values).**

$$\operatorname{range}\left(\lambda \langle p,q\rangle \mapsto \operatorname{dist}\left(p, q\right)\right) = \{0,u,v,1,2\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereSharpness.eight_exact_distance_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real u and v satisfying $0 < u < v < 1$, p and q range over Eight u v hu huv hv. The equality states exact occurrence of all five displayed values, not merely containment. The eight-point module establishes its order, exact original center and every sphere count via `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_card`, `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_center`, `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_zero_card`, `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_one_card` and `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_two_card`.

Together these declarations attain the lower bound with the two fixed lower-gap distances and no distance strictly between one and two. They do not assert that two auxiliary values are necessary in every gap of every count sequence.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_center`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_one_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_two_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_zero_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereSharpness.eight_exact_distance_values`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereSharpness.order_eight_and_two_gap_distances`
- Dependency: [D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight](UltrametricCenterSphereEight.md)
- Dependency: [D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders](UltrametricCenterSphereOrders.md)
