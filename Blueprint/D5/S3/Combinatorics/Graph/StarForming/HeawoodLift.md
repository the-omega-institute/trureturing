# All Heawood signings and connectivity

## Abstract

All Heawood signings and connectivity

The twenty-one binary Fano flags define the actual fourteen-vertex graph and binary lift. The linear invariant vanishes exactly for vertex coboundaries on that graph. Equal invariants give sheet-switching graph isomorphisms, and connectedness is equivalent to a nonzero invariant.

**Definition 1.1 (Vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.Vertex` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Vertex.

**Definition 1.2 (point).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.point`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.point` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def point (e : Fin 21) : Vertex.

**Definition 1.3 (line).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.line`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.line` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def line (e : Fin 21) : Vertex.

**Definition 1.4 (incident).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.incident`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.incident` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def incident (e : Fin 21) (v w : Vertex) : Prop.

**Definition 1.5 (base).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.base`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.base` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def base : SimpleGraph Vertex.

**Definition 1.6 (edgeIndex).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.edgeIndex`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.edgeIndex` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def edgeIndex (v w : Vertex) : Fin 21.

**Theorem 1.7 (base preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.base_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.base_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem base_preconnected : base.Preconnected.

**Definition 1.8 (voltage).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.voltage`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.voltage` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def voltage (s : Signing) : BinaryLift.Voltage base.

**Definition 1.9 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev graph (s : Signing).

**Theorem 1.10 (coboundary iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.coboundary_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.coboundary_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem coboundary_iff (s : Signing) : (∃ t : Switches, ∀ v w, base.Adj v w → s (edgeIndex v w)=t v+t w) ↔ phi s=0.

**Theorem 1.11 (preconnected iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.preconnected_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.preconnected_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem preconnected_iff (s : Signing) : (graph s).Preconnected ↔ phi s≠0.

**Theorem 1.12 (isomorphic of phi eq).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.isomorphic_of_phi_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.isomorphic_of_phi_eq` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem isomorphic_of_phi_eq (s t : Signing) (h : phi s=phi t) : Nonempty (graph s ≃g graph t).

**Definition 1.13 (signingOfVoltage).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.signingOfVoltage`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.signingOfVoltage` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def signingOfVoltage (s : BinaryLift.Voltage base) : Signing.

**Definition 1.14 (voltageIso).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.voltageIso`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.voltageIso` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def voltageIso (s : BinaryLift.Voltage base) : BinaryLift.graph base s ≃g graph (signingOfVoltage s).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.base`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.base_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.coboundary_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.edgeIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.incident`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.isomorphic_of_phi_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.line`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.point`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.preconnected_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.signingOfVoltage`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.voltage`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodLift.voltageIso`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BinaryLift](BinaryLift.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching](HeawoodSwitching.md)
