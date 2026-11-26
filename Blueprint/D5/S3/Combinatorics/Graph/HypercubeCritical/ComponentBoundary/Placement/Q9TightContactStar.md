# Tight contacts force full stars

## Abstract

Signed boundary cancellation constrains tight minimum contact families.

**Theorem 1.1 (The full star and its antipodal copy).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar.tight_contact_cell_full_star`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar.tight_contact_cell_full_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complementary flips match the two contacting parity slices after an antipodal flip. Two distinct vertices of this common slice differ on exactly two axes. A row at distance three from a slice vertex is too close to its antipode in the opposite support. An occupied direction outside the cell would create a minimum displacement outside the tight family. The even boundary equation therefore counts only neighbors in the cell.

The common slice consists of every leaf of a star on the tight axis set. The two-spoke rows cancel, and the negative Huang sign around each square makes the unit contributions at the star center equal. Cubicity excludes the center. Cancellation there uses at least as many exterior directions as there are leaves.

**Theorem 1.2 (Strictness at distance three or more).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar.minimum_displacements_card_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar.minimum_displacements_card_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality in the binomial lower bound gives a cell on d + 2 axes. The full-star bound requires twice this number to be at most nine. Thus a nonempty parity family at distance three has at least eleven displacements, and one at distance four has at least sixteen.

**Theorem 1.3 (Strictness for a fixed saturated component pair).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar.minimum_displacements_card_strict_of_signed_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar.minimum_displacements_card_strict_of_signed_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weighted signed-defect singularity of each balanced connected cubic support provides the needed exterior cancellation on either parity. This supplies the strict count for the component pairs studied in Hong, Wu and Xia’s Problem 2. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar.minimum_displacements_card_strict`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar.minimum_displacements_card_strict_of_signed_defect`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar.tight_contact_cell_full_star`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ActualMinimumDisplacements](Q9ActualMinimumDisplacements.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactComplement](Q9TightContactComplement.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary](../Q9SignedFragmentBoundary.md)
