# Actual binary voltage covers

## Abstract

Actual binary voltage covers

A symmetric binary voltage on actual base edges defines the actual two-sheet graph. Vertex switches and the deck flip are graph isomorphisms. Projection is locally bijective. Over a preconnected base with an explicit vertex, the lift is preconnected exactly when the voltage is not a vertex coboundary. No finite list of base graphs or cover sizes is assumed.

**Definition 1.1 (F2).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.F2`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.F2` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev F2.

**Definition 1.2 (Voltage).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.Voltage`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.Voltage` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: structure Voltage.

**Definition 1.3 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (s : Voltage G) : SimpleGraph (V × F2).

**Definition 1.4 (switched).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.switched`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.switched` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def switched (s : Voltage G) (t : V → F2) : Voltage G.

**Definition 1.5 (switchIso).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.switchIso`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.switchIso` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def switchIso (s : Voltage G) (t : V → F2) : graph G s ≃g graph G (switched G s t).

**Definition 1.6 (flipIso).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.flipIso`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.flipIso` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def flipIso (s : Voltage G) : graph G s ≃g graph G s.

**Theorem 1.7 (cover).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.cover` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cover (s : Voltage G) : CoverPullback.NeighborhoodCover G.Adj (graph G s).Adj Prod.fst.

**Theorem 1.8 (preconnected iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.preconnected_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.preconnected_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem preconnected_iff (s : Voltage G) (hG : G.Preconnected) (r : V) : (graph G s).Preconnected ↔ ¬ ∃ t : V → F2, ∀ v w, G.Adj v w → s.sign v w=t v+t w.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.F2`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.Voltage`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.cover`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.flipIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.preconnected_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.switchIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/BinaryLift.switched`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Isomorphism](Isomorphism.md)
