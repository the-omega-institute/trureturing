# Rigidity of transverse cut boxes

## Abstract

The common height and odd incidence of transverse boxes determine their cut.

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

Overlaps propagate the center. The Hamming distance between the cut membership signatures of two axes counts the boxes containing the corresponding translated pair. Distinct signatures therefore have opposite parity, which forces all nonconstant cuts to separate the same pairs.

**Theorem 1.3 (Common stars give odd fibers in the quotient).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_realized_common_star_boxes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_realized_common_star_boxes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A transverse component fixes the deleted coordinate pattern, so the three leaves of an occupied common star project to three different transverse components. The connected support then gives the hypotheses of the cut rigidity theorem. The argument applies to the common-block branch of the Laurent approach to Hong, Wu and Xia’s Problem 2 once the transverse box realization is supplied.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.center_eq_of_overlap`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_connected_odd_box_fibers`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes.same_cut_of_realized_common_star_boxes`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentTransverseFibers](Q9LaurentTransverseFibers.md)
