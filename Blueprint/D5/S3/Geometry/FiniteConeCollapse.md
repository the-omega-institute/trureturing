# Finite cone collapse

## Abstract

Coordinate truncation and cone contraction give a based equivalence for the actual cone quotient.

**Definition 1.1 (Finite subcomplex data).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.SubcomplexPair`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.SubcomplexPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An ambient finite complex, an included subcomplex, and an actual face of the subcomplex suffice for the coordinate collar. No cone apex, full-subcomplex condition, collar, or extension property is supplied.

## Distance control by outside mass

SubcomplexPair.delta: Take the minimum over actual subcomplex faces of the sum of coordinates outside the face. Finiteness and the supplied face witness make this minimum defined.

## Normalized coordinate truncation

SubcomplexPair.deform: At time s truncate each coordinate x(v) to max(x(v)-s*min(delta,epsilon),0), then divide by the sum. Here epsilon is one divided by twice (card(V)+1). Every original face and every absent vertex coordinate is retained.

**Theorem 1.2 (Coordinate simplex data).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.simplex_data`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.simplex_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each realization point has nonnegative coordinates summing to one, as read from its actual face witness.

## Continuous coordinates

SubcomplexPair.coord_continuous: Coordinate evaluation is continuous in the original subspace topology.

**Theorem 1.3 (The actual finite face collection).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.mem_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.mem_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filtering all finite vertex subsets gives exactly the specified subcomplex faces.

**Theorem 1.4 (An inhabited face collection).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.faces_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.faces_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied subcomplex face is retained by the finite face filter.

**Theorem 1.5 (Nonnegative outside mass).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.outsideMass_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.outsideMass_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Outside mass is a finite sum of nonnegative coordinates.

**Theorem 1.6 (Continuous outside mass).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.continuous_outsideMass`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.continuous_outsideMass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each outside mass is a finite sum of continuous coordinate functions.

## Nonnegative face minimum

SubcomplexPair.delta_nonneg: The minimum of the actual outside masses is nonnegative.

## Continuous face minimum

SubcomplexPair.continuous_delta: The face collection is fixed and finite, so its inhabited minimum of continuous outside masses is continuous.

**Theorem 1.7 (An attaining face).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.delta_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.delta_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A face of the actual subcomplex attains the finite minimum, without any chosen vertex or cone structure.

**Theorem 1.8 (Control of each exterior coordinate).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.outside_coord_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.outside_coord_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coordinate outside a face is bounded by that face's outside mass, using coordinate nonnegativity.

## Exact vanishing locus

SubcomplexPair.delta_eq_zero_iff: If the minimum is zero, its attaining face contains the whole support by the exterior-coordinate bound. Conversely the face representing a subcomplex point has zero outside mass. Thus delta vanishes exactly on the actual realized subcomplex.

## Positive truncation scale

SubcomplexPair.epsilon_pos: For a SubcomplexPair V, one divided by twice (card(V)+1) is positive. The pair's face witness requires at least one vertex. When V is empty, the unrestricted FiniteSubcomplexCylinder.retraction takes its no-faces branch and projects to the bottom.

**Theorem 1.9 (The total truncation budget).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.card_mul_epsilon`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.card_mul_epsilon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertex count times epsilon is at most one half.

**Theorem 1.10 (Nonnegative truncation threshold).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.theta_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.theta_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The smaller of delta and epsilon is nonnegative.

**Theorem 1.11 (Uniform denominator bound).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.denominator_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.denominator_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each truncated coordinate is at least x(v)-epsilon. Summing and using the coordinate sum one and the total truncation budget gives a denominator at least one half for every point and every time.

**Theorem 1.12 (A positive normalizer).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.denominator_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.denominator_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform one-half lower bound makes every normalization denominator positive.

**Theorem 1.13 (Exact face preservation).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.deform_mem_face`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.deform_mem_face` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization preserves nonnegativity and total mass one; coordinates outside the original face remain zero after truncation. Thus the deformation stays inside that original affine face.

## Jointly continuous deformation

SubcomplexPair.continuous_deform: The coordinatewise maximum and fixed finite sum are continuous, and the denominator never vanishes. Subtype continuity gives continuity jointly in time and point.

## The exact initial map

SubcomplexPair.deform_zero: At time zero the coordinates are unchanged and the normalizer is one.

## Exact subcomplex fixing

SubcomplexPair.deform_fixed: On the subcomplex delta is zero. Every truncated coordinate and the normalizer are unchanged at every time, hence every subcomplex point is fixed exactly.

**Theorem 1.14 (Collar entry into an actual face).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.deform_one_mem_subcomplex`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.deform_one_mem_subcomplex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When delta is at most epsilon, choose a subcomplex face attaining delta. Every coordinate outside it is at most delta and is killed by time-one truncation. The normalized endpoint lies in that actual subcomplex face.

**Definition 1.15 (Coordinate face simplices).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.faceSimplex`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.faceSimplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite vertex type V and a finite subset s, the face simplex consists of real coordinate vectors with nonnegative entries summing to one and with every coordinate outside s equal to zero. The simplex of the empty face is empty.

**Theorem 1.16 (Actual affine simplices).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.faceSimplex_eq_convexHull`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteConeCollapse.faceSimplex_eq_convexHull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite subset s of V, its coordinate simplex equals the convex hull in the real coordinate space of the coordinate vertices indexed by s. Thus the coordinate model is the usual geometric simplex, including its boundary faces.

**Definition 1.17 (Finite geometric realization).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.realization`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.realization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The realization of a Mathlib pre-abstract simplicial complex is the union of its actual coordinate face simplices, with the subspace topology inherited from the finite real coordinate space. The ambient vertex type may contain vertices absent from the complex.

**Definition 1.18 (An actual cone subcomplex).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.ConePair`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.ConePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A cone pair consists of an ambient complex M, a subcomplex C, and an apex p whose singleton is a face of C. Adjoining p to any face of C again gives a face of C. These are face conditions on the given complexes, and do not assert any extension property or homotopy equivalence. The singleton cone is included.

**Definition 1.19 (The realized subcomplex).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.coneSet`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.coneSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Inside the ambient coordinate realization, the cone set is exactly the set of points belonging to the coordinate realization of C.

**Definition 1.20 (The based coordinate vertex).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.apexPoint`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.apexPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The basepoint is the coordinate vector with entry one at p and zero at every other vertex.

**Definition 1.21 (Coordinate truncation and cone contraction).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.controlledHomotopy`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.controlledHomotopy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each cone face, sum the coordinates outside that face, and take the minimum of these finitely many sums. This continuous nonnegative function vanishes exactly on the cone. Truncate every coordinate by the smaller of that minimum and 1 divided by twice the number of ambient vertices plus two, then normalize. Throughout the unit interval the denominator is at least one half, the support stays in the original face, and points sufficiently near the cone enter an actual cone face. A continuous collar coefficient then turns on the linear contraction to p only after truncation has reached that face. The resulting ambient homotopy starts at the identity, preserves the cone, finishes by sending the cone to p, and fixes p throughout.

**Definition 1.22 (The actual collapse relation).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.collapseSetoid`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.collapseSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two points are related exactly when they are equal or both belong to the realized cone. The quotient carries the quotient topology.

**Definition 1.23 (The continuous quotient map).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.quotientMap`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.quotientMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map sends a point to its class under the actual collapse relation.

**Definition 1.24 (An explicit continuous inverse up to homotopy).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.collapseInverse`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.collapseInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The final controlled deformation is constant on every collapse fiber. Its quotient lift is the continuous inverse map and sends the cone class to p.

**Definition 1.25 (Both based inverse homotopies).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.basedCollapse`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.basedCollapse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient controlled deformation is a homotopy from the identity to the quotient map followed by the inverse, relative to p. Composing the deformation with the quotient map is constant on each collapse fiber at every time, so it descends to the second homotopy, from the quotient identity to the inverse followed by the quotient map, relative to the cone class. Joint continuity follows from Mathlib's quotient-product lifting theorem using local compactness of the unit interval.

**Definition 1.26 (Based homotopy equivalence of the actual quotient).**

Lean statement: `D5/S3/Geometry/FiniteConeCollapse.collapseEquiv`

*Formalization.* `D5/S3/Geometry/FiniteConeCollapse.collapseEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite cone pair, the actual quotient map is a homotopy equivalence with the displayed inverse and both displayed based homotopies. This is the finite cone collapse lemma. It does not settle the additional join, graph substitution, or zero-vertex conventions of Carnero Bravo's Question 22.

## References

- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.ConePair`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.SubcomplexPair`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.apexPoint`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.basedCollapse`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.card_mul_epsilon`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.collapseEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.collapseInverse`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.collapseSetoid`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.coneSet`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.continuous_outsideMass`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.controlledHomotopy`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.deform_mem_face`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.deform_one_mem_subcomplex`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.delta_witness`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.denominator_bound`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.denominator_pos`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.faceSimplex`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.faceSimplex_eq_convexHull`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.faces_nonempty`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.mem_faces`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.outsideMass_nonneg`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.outside_coord_le`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.quotientMap`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.realization`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.simplex_data`
- Truth anchor: `D5/S3/Geometry/FiniteConeCollapse.theta_nonneg`
