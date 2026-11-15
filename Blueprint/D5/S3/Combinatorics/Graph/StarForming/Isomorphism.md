# Graph isomorphisms preserve actual finite maxima

## Abstract

Graph isomorphisms preserve actual finite maxima

Actual selected images transport formation, inclusion-minimality and dissociation in both directions. The finite maxima beta and SF are invariant, with actual attaining images. Empty finite types are included.

**Theorem 1.1 (minimal image iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Isomorphism.minimal_image_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Isomorphism.minimal_image_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_image_iff (e : G ≃g H) (S : Finset V) : IsMinimalStarForming H 2 (S.image e) ↔ IsMinimalStarForming G 2 S.

**Theorem 1.2 (independent image iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Isomorphism.independent_image_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Isomorphism.independent_image_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem independent_image_iff (e : G ≃g H) (S : Finset V) : IsKIndependent H 2 (S.image e) ↔ IsKIndependent G 2 S.

**Theorem 1.3 (parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Isomorphism.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Isomorphism.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameters (e : G ≃g H) : beta G 2 = beta H 2 ∧ SF G 2 = SF H 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Isomorphism.independent_image_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Isomorphism.minimal_image_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Isomorphism.parameters`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Comparison](Comparison.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteCover](FiniteCover.md)
