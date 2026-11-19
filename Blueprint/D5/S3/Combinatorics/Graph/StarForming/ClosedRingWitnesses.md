# Actual module selections and deletion failures

## Abstract

Actual module selections and deletion failures

The original thirty-six forming selection has explicit deletion failures. The displayed thirty-three dissociation selection, local bipartition and open-port states are kernel checked. These are local certificate inputs to the arbitrary finite symbolic assembly, not a finite enumeration of ring orders.

**Definition 1.1 (forming).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.forming`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.forming` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def forming (v : Fin 62) : Prop.

**Definition 1.2 (failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.failure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.failure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def failure (v : Fin 62) : Fin 62.

**Definition 1.3 (independent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.independent`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.independent` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def independent (v : Fin 62) : Prop.

**Theorem 1.4 (forming certificates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.forming_certificates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.forming_certificates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_certificates : Regular.Minimal graph.Adj forming ∧ (Finset.univ.filter forming).card=36.

**Theorem 1.5 (independent certificates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.independent_certificates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.independent_certificates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem independent_certificates : DissociationCover.Dissociates graph.Adj independent ∧ (Finset.univ.filter independent).card=33.

**Definition 1.6 (color).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.color`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.color` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def color (v : Fin 62) : Fin 2.

**Theorem 1.7 (local class).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.local_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.local_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem local_class : (∀ v w : Fin 62, graph.Adj v w → color v≠color w) ∧ (∀ v : Fin 62, (neighbors v).Nodup) ∧ (∀ v : Fin 62, (neighbors v).length=if v=12 ∨ v=17 then 2 else 3).

**Theorem 1.8 (interface states).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.interface_states`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.interface_states` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem interface_states : ¬ forming 12 ∧ ¬ forming 17 ∧ independent 12 ∧ ¬ independent 17 ∧ color 12=0 ∧ color 17=1.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.color`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.forming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.forming_certificates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.independent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.independent_certificates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.interface_states`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses.local_class`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClosedModule](ClosedModule.md)
