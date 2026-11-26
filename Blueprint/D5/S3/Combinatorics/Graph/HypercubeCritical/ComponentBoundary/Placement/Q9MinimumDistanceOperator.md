# The signed coordinate action constrains minimum displacements

## Abstract

Minimum-distance contacts between weighted cube supports.

**Definition 1.1 (Parity of a flip word).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.wordParity`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.wordParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each axis in the word toggles the starting parity.

**Definition 1.2 (A ridge and one extension).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.RidgeContact`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.RidgeContact` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Flip the ordered ridge axes and then the extension axis at a vertex of the specified parity in the first support. The extension is absent from the ridge and the endpoint belongs to the second support.

**Definition 1.3 (Active extension axes).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.RidgeActiveAxis`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.RidgeActiveAxis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An axis is active if the extended ridge realizes a contact.

**Definition 1.4 (A cell of contact endpoints).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.SameContactCell`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.SameContactCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two endpoints agree at every coordinate except the other active extensions of the ridge.

**Theorem 1.5 (Signed cancellation inside each cell).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimum_distance_contact_cell_cancels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimum_distance_contact_cell_cancels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two vectors are supported exactly on the selected endpoint parities. The unit-weight image stays in the second support and the image with the chosen coordinate doubled stays in the first. Every cell has signed contact sum zero.

A signed word shorter than the separation distance has zero pairing across the supports. A repeated axis disappears by the square identity, and each new axis passes the ridge word with the same anticommutation sign. Project onto a coordinate cell and compare the two weightings. The sum in one cell is twice the sum in the cell obtained by flipping the doubled axis. The coordinate involution forces both to vanish.

**Theorem 1.6 (A companion with the same displacement).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimum_distance_contact_has_companion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimum_distance_contact_has_companion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One contact would produce a nonzero signed sum. Thus each contact has a distinct companion with the same displacement in the same cell.

**Definition 1.7 (The family of realized displacements).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimumDisplacements`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimumDisplacements` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Record the differing axes of each pair at the specified distance whose first endpoint has the given parity.

**Theorem 1.8 (The number and equality case of minimum displacements).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimum_displacements_card_and_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimum_displacements_card_and_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two different vertices on the same parity disagree on at least two coordinates. The agreement with the companion therefore supplies at least two other extensions at every ridge. The count of the uniform family gives at least (d + 2) choose 2 displacements at minimum distance d.

If equality holds, the displacements are precisely the d-subsets of one set of d + 2 axes. Its hypotheses specify the weighted support conditions needed for the two components in Hong, Wu and Xia’s Problem 2. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.RidgeActiveAxis`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.RidgeContact`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.SameContactCell`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimumDisplacements`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimum_displacements_card_and_equality`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimum_distance_contact_cell_cancels`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.minimum_distance_contact_has_companion`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator.wordParity`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/MinimumContactDisplacementCount](MinimumContactDisplacementCount.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells](../Q9SignedContactCells.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointEightWord](../../TwentyPointEightWord.md)
