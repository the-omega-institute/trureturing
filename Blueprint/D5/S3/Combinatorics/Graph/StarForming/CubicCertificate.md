# Rewiring away from selected vertices

## Abstract

Rewiring away from selected vertices

Rewiring edges whose endpoints are both outside the fixed selection preserves formation for every smaller selection and therefore inclusion-minimality. The arbitrary vertex type and the agreement condition remain explicit. The Fano incidence table, eight-set and deletion witnesses belong with their exact maxima and refutation in HeawoodParameters.

**Theorem 1.1 (forms rewiring).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.forms_rewiring`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.forms_rewiring` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forms_rewiring {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection smaller : Vertex → Prop) (hsubset : ∀ vertex, smaller vertex → selection vertex) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) (hforms : Forms original smaller) : Forms modified smaller.

**Theorem 1.2 (minimal rewiring forward).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring_forward`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring_forward` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_rewiring_forward {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) (hminimal : Minimal original selection) : Minimal modified selection.

**Theorem 1.3 (minimal rewiring).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_rewiring {Vertex : Type} (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop) (hagreement : ∀ first second, selection first ∨ selection second → (original first second ↔ modified first second)) : Minimal original selection ↔ Minimal modified selection.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.forms_rewiring`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicCertificate.minimal_rewiring_forward`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularBound](RegularBound.md)
