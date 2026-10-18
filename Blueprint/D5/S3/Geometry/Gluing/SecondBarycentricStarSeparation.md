# The 1/24 separation and 1/48 neighborhood core

## Abstract

Coordinate separation and disjoint ambient neighborhoods for second stars

This module formalizes the arithmetic and sup-norm part of CFMP §§69.4–69.5. The carrier is the standard coordinate simplex of Fin(4), and the coordinate-star region at i consists of points whose i-th coordinate is at least 25/48. These regions are the coordinate envelopes supplied by the §69.3 bound. The module proves their 1/24 separation and the disjointness of their radius-r ambient neighborhoods for 0 < r < 1/48.

**Definition 1.1 (The standard coordinate simplex).**

$$\forall x \in Fin\left(4\right) \to R,\; (x \in standardSimplex\left(\right)) \iff ((\forall i \in Fin\left(4\right),\; 0 \le x\left(i\right)) \land (sum\left(x\right) = 1))$$

*Formalization.* `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.standardSimplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinates are real functions on Fin(4). The carrier keeps nonnegative entries and total coordinate sum one.

**Definition 1.2 (The 25/48 coordinate envelope of a star).**

$$\forall i \in Fin\left(4\right),\; \forall x \in Coordinate,\; (x \in coordinateStarRegion\left(i\right)) \iff ((x \in standardSimplex\left(\right)) \land (div\left(25, 48\right) \le x\left(i\right)))$$

*Formalization.* `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinateStarRegion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the coordinate region forced by the sharp §69.3 lower bound. Its membership is a coordinate envelope; identifying it with the actual geometric closed star requires the separate second-subdivision bridge.

**Definition 1.3 (An ambient sup-norm neighborhood).**

$$\forall i \in Fin\left(4\right),\; \forall r \in R,\; \forall z \in Coordinate,\; (z \in coordinateStarNeighborhood\left(i, r\right)) \iff (\exists x \in Coordinate,\; (x \in coordinateStarRegion\left(i\right)) \land (norm\left(z - x\right) < r))$$

*Formalization.* `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinateStarNeighborhood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Lean definition is a union of metric balls centered at all points of the coordinate-star region. The displayed existential form is the corresponding pointwise membership description.

**Theorem 1.4 (Distinct coordinate regions are disjoint).**

$$\forall i \in Fin\left(4\right),\; \forall j \in Fin\left(4\right),\; (i \neq j) \implies (Disjoint\left(coordinateStarRegion\left(i\right), coordinateStarRegion\left(j\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_regions_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common point would have two distinct coordinates at least 25/48, while all four nonnegative coordinates sum to one. Their sum would exceed one, giving a contradiction.

**Theorem 1.5 (Distinct regions have 1/24 sup-norm separation).**

$$\forall i \in Fin\left(4\right),\; \forall j \in Fin\left(4\right),\; (i \neq j) \implies (\forall x \in Coordinate,\; \forall y \in Coordinate,\; ((x \in coordinateStarRegion\left(i\right)) \land (y \in coordinateStarRegion\left(j\right))) \implies (div\left(1, 24\right) \le norm\left(x - y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_regions_separated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x in the i-region and y in the j-region, the simplex sum gives y_i <= 23/48. Hence x_i-y_i >= 1/24. The i-th coordinate is bounded by the sup norm of x-y, yielding the displayed separation.

**Theorem 1.6 (Coordinate neighborhoods are open).**

$$\forall i \in Fin\left(4\right),\; \forall r \in R,\; (0 < r) \implies (IsOpen\left(coordinateStarNeighborhood\left(i, r\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_neighborhood_isOpen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each neighborhood is a union of open metric balls, so it is open in the ambient function-space norm topology.

**Theorem 1.7 (Each region lies in its neighborhood).**

$$\forall i \in Fin\left(4\right),\; \forall r \in R,\; (0 < r) \implies (subset\left(coordinateStarRegion\left(i\right), coordinateStarNeighborhood\left(i, r\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_region_subset_neighborhood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every region point is the center of one of the balls in the union, so the corresponding region is contained in every positive-radius neighborhood.

**Theorem 1.8 (Radius below 1/48 keeps distinct neighborhoods disjoint).**

$$\forall i \in Fin\left(4\right),\; \forall j \in Fin\left(4\right),\; (i \neq j) \implies (\forall r \in R,\; ((0 < r) \land (r < div\left(1, 48\right))) \implies (Disjoint\left(coordinateStarNeighborhood\left(i, r\right), coordinateStarNeighborhood\left(j, r\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_neighborhoods_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an ambient point belonged to two neighborhoods, the triangle inequality would make the distance between their centers strictly less than 2r. For r<1/48 this contradicts the 1/24 separation.

Together with the §69.3 coordinate enclosure, these statements supply the arithmetic core of §§69.4–69.5. They do not identify actual face-quotient stars with these regions, prove cross-chart compatibility, or establish a neighborhood in a glued manifold.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinateStarNeighborhood`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinateStarRegion`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_neighborhood_isOpen`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_neighborhoods_disjoint`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_region_subset_neighborhood`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_regions_disjoint`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.coordinate_star_regions_separated`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricStarSeparation.standardSimplex`
