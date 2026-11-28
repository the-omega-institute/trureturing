# Translations forced by three-mask cuts in the nine-cube

## Abstract

Three-mask axis cuts generate translations of contact fibres. Composing the translations from two cuts can force a further mask.

For Hong–Wu–Xia Problem 2 (arXiv:2610.09483v1), consider distance-two contacts on one parity between separated balanced cubic components. Axis cuts restrict which pairs of flips can occur in the mixed part of the Huang operator.

**Theorem 1.1 (At least three masks across each nonempty cut).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.every_nonempty_axis_cut_has_three_masks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.every_nonempty_axis_cut_has_three_masks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed row vanishes at each contact endpoint. A single mask cannot cancel. Two masks force an alternating square whose opposite rows are incompatible after doubling a coordinate of only one mask.

**Theorem 1.2 (Even crossing degree).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.even_crossing_contact_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.even_crossing_contact_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At unit weights each incident term of the mixed row is a switching sign, so the zero row contains equally many positive and negative terms.

**Theorem 1.3 (Two edges at every incident point of a three-mask cut).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.crossing_contact_degree_two_of_small_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.crossing_contact_degree_two_of_small_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each mask has one oriented representative across the cut and at most one contact at a given vertex. The cut bound and even crossing degree force degree two at every incident vertex.

**Theorem 1.4 (The product of the other two masks preserves each contact fibre).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.three_mask_cut_preserves_contact_fibre`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.three_mask_cut_preserves_contact_fibre` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each endpoint there is exactly one edge to continue along. The weight argument prevents the continuation from closing an alternating square. The second traversal of the initial mask therefore realizes the translate by the product of the other two masks.

**Theorem 1.5 (Two cuts force another mask).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.two_three_mask_cuts_force_contact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.two_three_mask_cuts_force_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shifts of the shared contact fibre can be composed. When the product moves precisely two axes, composing with the original contact can cancel one of them and force a new distance-two displacement. For the cuts through the mask {2,6} on {2} and {0,3,5,6} with companion masks {2,7}, {2,8} and {0,7}, {6,8}, the forced mask is {0,2}.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.crossing_contact_degree_two_of_small_cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.even_crossing_contact_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.every_nonempty_axis_cut_has_three_masks`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.three_mask_cut_preserves_contact_fibre`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut.two_three_mask_cuts_force_contact`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCenter](Q9TightDistanceTwoCenter.md)
