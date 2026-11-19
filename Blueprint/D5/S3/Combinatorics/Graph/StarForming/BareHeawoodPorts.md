# Failure shapes at bare boundary ports

## Abstract

Failure shapes at bare boundary ports

When an internal deletion failure has no internal supporting explanation, its boundary support forces the displayed bare-port conditions. The companion theorem identifies omitted internal neighbors. These generic statements are not the finite Fano inequality |C|+t<=8, which requires the separate complete local case proof.

**Theorem 1.1 (only failure forces bare boundary).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BareHeawoodPorts.only_failure_forces_bare_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BareHeawoodPorts.only_failure_forces_bare_boundary` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem only_failure_forces_bare_boundary {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (deleted port support : Vertex) (hminimal : Minimal adjacency selection) (hdeleted : selection deleted) (hnew : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) (hother : ∀ outside, ¬ selection outside → outside ≠ port → TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside) (hsupport : selection support) (hkeep : support ≠ deleted) (hedge : adjacency port support) (hnotdeleted : ¬ adjacency port deleted) : ¬ selection port ∧ ∀ neighbor, adjacency port neighbor → selection neighbor → neighbor = support.

**Theorem 1.2 (internal neighbors omitted).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BareHeawoodPorts.internal_neighbors_omitted`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BareHeawoodPorts.internal_neighbors_omitted` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem internal_neighbors_omitted {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection internal : Vertex → Prop) (port support : Vertex) (hboundary : ¬ selection port ∧ ∀ neighbor, adjacency port neighbor → selection neighbor → neighbor = support) (hexternal : ¬ internal support) : ¬ selection port ∧ ∀ neighbor, internal neighbor → adjacency port neighbor → ¬ selection neighbor.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BareHeawoodPorts.internal_neighbors_omitted`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BareHeawoodPorts.only_failure_forces_bare_boundary`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularBound](RegularBound.md)
