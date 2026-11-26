# Rigidity of transverse cut boxes

## Abstract

A family of balanced transverse cut boxes connected by overlaps has a common center and a single unordered cut if the boxes share an integer height with the stated offset law and each occupied point has odd multiplicity.

**Theorem 1.1 (Integer height determines the common center).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.center_eq_of_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.center_eq_of_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translate one shared point to zero by symmetric difference. Each relative center then consists of two crossing axes. If the centers differ, the crossing pairs can be rearranged to produce another shared point that changes an axis on which the centers disagree. The two height differences on that axis have opposite signs.

**Theorem 1.2 (Odd incidence determines the unordered cut).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_connected_odd_box_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_connected_odd_box_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the cut boxes are balanced and any two are linked by a chain of overlaps, all boxes share an integer height with the stated offset law, and each occupied point lies in an odd number of boxes. The overlap chains propagate a common center throughout the family. The Hamming distance between the cut membership signatures of two axes counts the boxes containing the corresponding translated pair. Distinct signatures therefore have opposite parity, which forces all nonconstant cuts to separate the same pairs.

**Theorem 1.3 (Common stars give odd fibers in the quotient).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_realized_common_star_boxes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_realized_common_star_boxes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the common-star cover induces a connected subgraph of the nine-dimensional cube and the encoded projection of each transverse component is exactly the point set of its balanced cut box. The boxes share an integer height with the stated offset law, and each two-step move between side vertices stays in its component or preserves the projection. These moves connect the family of boxes by overlaps. Each occupied point then lies in exactly three boxes indexed by distinct transverse components. The three leaves of a common star differ in the deleted coordinates, which are fixed within a component. This supplies the odd incidence needed to treat the common-block branch of the Laurent approach to Hong, Wu and Xia’s Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.center_eq_of_overlap`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_connected_odd_box_fibers`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_realized_common_star_boxes`
- Dependency: [D5/S3/Combinatorics/Graph/HereditaryFlip/Metric](../../../HereditaryFlip/Metric.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentTransverseFibers](Q9LaurentTransverseFibers.md)
