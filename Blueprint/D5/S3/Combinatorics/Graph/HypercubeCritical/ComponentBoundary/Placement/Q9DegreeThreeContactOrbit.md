# Coordinate translations at cubic contact axes

## Abstract

A cubic contact axis forces a simultaneous translation of both endpoints.

**Theorem 1.1 (Forced translation of a contact).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit.translated_contact_of_three_partners`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit.translated_contact_of_three_partners` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weighted exterior cancellation forces the contact to recur after both endpoints are toggled in the other two partner coordinates.

**Theorem 1.2 (The two directions through a contact midpoint).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit.exterior_midpoint_directions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit.exterior_midpoint_directions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A shared midpoint with at most three candidate axes for one support has exactly two neighbors in that support by the parity of exterior degree.

**Theorem 1.3 (Square completion from contact translations).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit.three_partner_contact_completes_square`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit.three_partner_contact_completes_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the two incident axes both have exactly three partners, translated contacts and the midpoint rule complete a square through any two-edge walk along the incident edge.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit.exterior_midpoint_directions`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit.three_partner_contact_completes_square`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit.translated_contact_of_three_partners`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCenter](Q9TightDistanceTwoCenter.md)
