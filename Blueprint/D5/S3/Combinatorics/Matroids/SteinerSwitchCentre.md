# Central Points and Point-Deleted Steiner Switches

## Abstract

The centre of the Steiner loop determines which deletions admit a maximal switch.

**Definition 1.1 (Product in the Steiner loop).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.steinerMul`

*Formalization.* `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.steinerMul` (`✓ std3`).

*Citation.* Robert W. Quackenbush (1976). *Varieties of Steiner Loops and Steiner Quasigroups*. DOI: [10.4153/CJM-1976-118-1](https://doi.org/10.4153/CJM-1976-118-1). URL: <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00020873>.

*Commentary.*

Adjoin an identity to a finite complete Steiner triple system. Left multiplication by an original point is its matching translation. Left multiplication by the identity leaves every point fixed.

**Definition 1.2 (A deletion that admits a switch).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.AdmitsSwitch`

*Formalization.* `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.AdmitsSwitch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A deleted point admits a switch if the retained packing has a map whose partners are exactly its uncovered pairs and if some retained pivot and start satisfy the successful-switch predicate for that map.

**Theorem 1.3 (Maximal switches detect noncentral points).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.admits_switch_iff_not_central`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.admits_switch_iff_not_central` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a finite complete Steiner triple system on r+1 points, deleting an original point admits a maximal switch exactly when that point lies outside the centre of its Steiner loop. Centrality means commuting with every element and satisfying both the left and right association laws.

At an eligible start, the switch fails exactly when the two translations commute there. The adjoined identity, the deleted point, a retained pivot and the third point of their block form a commuting square. Together these cases show that failure at every retained pivot gives commutation on the whole carrier. In the commutative loop, interchanging the other two inputs converts this condition into the association laws.

**Theorem 1.4 (Counting the deletions that admit a switch).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.ncard_admits_switch`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.ncard_admits_switch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a finite complete Steiner triple system on r+1 points, the number of deleted points with some successful switch is r+2 minus the cardinality of the Steiner loop centre.

The original points admitting a switch embed onto the complement of the centre. The only adjoined point is the identity, which lies in the centre.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.AdmitsSwitch`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.admits_switch_iff_not_central`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.ncard_admits_switch`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSwitchCentre.steinerMul`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches](SteinerAlternatingSwitches.md)
