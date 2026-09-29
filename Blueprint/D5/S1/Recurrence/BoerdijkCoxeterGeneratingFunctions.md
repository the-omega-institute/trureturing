# Tetrahelix Coordinate Generating Functions

## Abstract

The ordered Boerdijk-Coxeter tetrahelix has Kagey's three exact rational coordinate series.

The vertices begin in the source's order: (-1,-1,-1), (-1,1,1), (1,-1,1), (1,1,-1). Each next vertex is the reflection of the oldest across the face through the other three. The source scales coordinates by one through index three and by a power of three thereafter.

**Definition 1.1 (Rational points).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.Point`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.Point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point has three rational coordinates, indexed by Fin 3.

**Definition 1.2 (Squared distance).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.sqDist`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.sqDist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of the three squared coordinate differences.

**Definition 1.3 (Face centroid).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.faceCenter`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.faceCenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinatewise average of three face vertices.

**Definition 1.4 (Reflected vertex).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.reflected`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.reflected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Twice the face centroid minus the oldest vertex, coordinate by coordinate.

**Definition 1.5 (Regular tetrahedron).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.regular`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.regular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six squared edge lengths of four vertices are equal.

**Definition 1.6 (Orthogonality to a face vertex).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.faceOrthogonal`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.faceOrthogonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector from the face centroid to the old vertex is perpendicular to the vector from that centroid to the selected face vertex.

**Definition 1.7 (Noncollinear face).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.faceNoncollinear`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.faceNoncollinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The third face vertex is not on the rational affine line through the first two.

**Definition 1.8 (Ordered helix vertices).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.vertex`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unique order-four recurrence solution with the source's ordered initial tetrahedron.

**Definition 1.9 (Coordinate scaling).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.scale`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.scale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor is one through index three, then 3 to the power n minus three.

**Definition 1.10 (Scaled coordinate).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.scaled`

*Formalization.* `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.scaled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected coordinate of vertex n multiplied by the source scaling factor.

**Theorem 1.11 (The three conjectured coordinate series).**

Lean statement: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a400216-a400218-tetrahelix-generating-functions` (proved) by `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a400216-a400218-tetrahelix-generating-functions","declaration_gid":"D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2026). *OEIS A400216, A400217 and A400218, Boerdijk-Coxeter tetrahelix coordinates*. URL: <https://oeis.org/A400216>.

*Commentary.*

For every natural index, the face has noncollinear vertices and a nonzero normal. The next vertex is its face reflection. The x, y and z generating functions equal the three rational formal power series in OEIS A400216, A400217 and A400218. The proof uses a scaled order-four recurrence and cancels one nonzero factor for z. The OEIS asymptotic comparison of 24 orientations is not part of the Lean statement.

## References

- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.Point`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.faceCenter`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.faceNoncollinear`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.faceOrthogonal`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.reflected`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.regular`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.result`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.scale`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.scaled`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.sqDist`
- Truth anchor: `D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.vertex`
