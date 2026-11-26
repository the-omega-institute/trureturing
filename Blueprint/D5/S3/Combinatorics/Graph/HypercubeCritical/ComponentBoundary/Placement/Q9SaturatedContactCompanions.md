# A two-axis contact forces a companion

## Abstract

Coordinate restrictions on contacts between saturated cube components.

**Definition 1.1 (Two-axis contact).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.TwoFlipContact`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.TwoFlipContact` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point of the selected parity of the first support is a contact if flipping two distinct named axes lands in the second support.

**Definition 1.2 (Active contact axis).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.ActiveAxis`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.ActiveAxis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With one axis fixed, another axis is active if some point on the selected parity gives a contact along the two axes.

**Theorem 1.3 (A companion in the same coordinate cell).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.two_flip_contact_has_companion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.two_flip_contact_has_companion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two disjoint supports with no edge between them and a vector supported exactly on one parity of each support. The weighted image of the first vector stays in the first vertex set when the weight of the second contact axis is doubled. The unit-weight image of the second vector stays in the second vertex set. Every contact has a distinct companion across the same two axes, agreeing on all coordinates except possibly the other active axes.

Freeze the coordinates outside the other active axes and project onto one cell. Separation makes the unit and weighted single-flip pairings zero. Anticommutation moves each weighted flip across the fixed flip. Inactive directions contribute zero and the other active directions leave the cell fixed. Subtracting the two identities gives the contact sum of this cell as twice the sum in the cell with the doubled coordinate flipped. Applying the same equality to that second cell makes both sums zero. One contact alone would contribute a nonzero product.

**Theorem 1.4 (At least three partners for an active axis).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.exists_two_components_with_two_flip_companions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.exists_two_components_with_two_flip_companions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any subcubic 258-point support has two distinct actual components that satisfy the companion condition on the false parity in both orders. Every active axis has at least three partners. The companion has the same parity, so it must differ in at least two coordinates, each another active axis. At exactly three partners it is the translate by the other two axes.

The positive internal Gram vector for each chosen weight has zero crossing to the exterior, by the weighted boundary Gram identity. Undoing the Huang switching and extending by zero supplies the two vectors. The components are chosen before the contact axes and weights. The result restricts joint placements in Hong, Wu and Xia’s open Problem 2. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.ActiveAxis`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.TwoFlipContact`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.exists_two_components_with_two_flip_companions`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions.two_flip_contact_has_companion`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells](../Q9SignedContactCells.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedBoundaryGram](../Q9WeightedBoundaryGram.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity](../../Translation/Q9TranslationAperiodicity.md)
