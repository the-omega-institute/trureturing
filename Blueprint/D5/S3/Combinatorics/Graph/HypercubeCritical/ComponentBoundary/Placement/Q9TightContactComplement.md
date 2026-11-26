# Complementary flips and antipodal slices

## Abstract

Coordinate symmetries at equality in the minimum displacement bound.

**Theorem 1.1 (The complementary axes preserve each contact).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactComplement.minimum_contact_flip_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactComplement.minimum_contact_flip_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the separated supports admit the weighted exterior cancellation functions in the statement. If the minimum displacements of length d on one parity are all d-subsets of d + 2 axes, fix a displacement and erase one axis. The only other active extensions are the two axes outside that displacement. The companion has the same parity and differs from the original endpoint, so it flips both axes. The two endpoints of the contact move together and keep the same displacement.

**Theorem 1.2 (The antipodal flip matches the slices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactComplement.minimum_contact_cell_antipodes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactComplement.minimum_contact_cell_antipodes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same weighted cancellation and tight-family hypotheses, fix the coordinates outside the d + 2 axes and compare a vertex of the first support with the antipode of a vertex of the second support on the same parity. Separation and the antipodal distance identity force their distance to be zero or two.

At distance zero the vertices already match. At distance two the original pair realizes the minimum distance, and the complementary flip puts each antipode in the other support. This gives antipodal matching in cells meeting both of the specified parity slices. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactComplement.minimum_contact_cell_antipodes`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactComplement.minimum_contact_flip_complement`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator](Q9MinimumDistanceOperator.md)
