# Exported private-clause ownership

## Abstract

Exported private-clause ownership

An unsupported selected nonport in a port-only ambient block has a witness beyond a selected port. The ExportWitness records the actual omitted external vertex, the selected port, its sole selected internal neighbor and the ambient deletion failure. Distinct exported owners cannot reuse that witness under the displayed hypotheses. No arithmetic block-loss or global no-reuse theorem is inferred without its additional graph counts.

**Definition 1.1 (ExportWitness).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.ExportWitness`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.ExportWitness` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def ExportWitness {Vertex : Type} (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop) (candidate boundary outside : Vertex) : Prop.

**Theorem 1.2 (unsupported has export).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.unsupported_has_export`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.unsupported_has_export` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem unsupported_has_export {Vertex : Type} (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop) (hinclusion : ∀ first second, inside first second → ambient first second) (hinside : ∀ first second, inside first second → core first ∧ core second) (hsymmInside : ∀ first second, inside first second → inside second first) (hsymmAmbient : ∀ first second, ambient first second → ambient second first) (hunchanged : ∀ vertex, core vertex → ¬ port vertex → ∀ neighbor, ambient vertex neighbor → inside vertex neighbor) (hminimal : Minimal ambient selection) (candidate : Vertex) (hcore : core candidate) (hnonport : ¬ port candidate) (hselected : selection candidate) (hunsupported : ¬ ∃ clause, Private inside (fun vertex => core vertex ∧ selection vertex) clause candidate) : ∃ boundary outside, ExportWitness inside ambient core port selection candidate boundary outside.

**Theorem 1.3 (exported owner unique).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.exported_owner_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.exported_owner_unique` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem exported_owner_unique {Vertex : Type} (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop) (first second firstBoundary secondBoundary outside : Vertex) (hfirst : ExportWitness inside ambient core port selection first firstBoundary outside) (hsecond : ExportWitness inside ambient core port selection second secondBoundary outside) (hcore : core second) (hselected : selection second) : first = second.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.ExportWitness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.exported_owner_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss.unsupported_has_export`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/PrivateClauses](PrivateClauses.md)
