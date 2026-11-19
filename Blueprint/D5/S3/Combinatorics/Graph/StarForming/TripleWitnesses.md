# Original triple-port forming and dissociation witnesses

## Abstract

Original triple-port forming and dissociation witnesses

The original selected twenty-eight-set, actual deletion failures, dissociation twenty-six-set and bipartition are checked on the forty-eight-vertex open module. Both seam vertices are unselected in the forming witness; only the even seam vertex belongs to the dissociation witness.

**Definition 1.1 (forming).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.forming`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.forming` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def forming (v : Fin 48) : Prop.

**Definition 1.2 (failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.failure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.failure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def failure (v : Fin 48) : Fin 48.

**Definition 1.3 (independent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.independent`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.independent` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def independent (v : Fin 48) : Prop.

**Theorem 1.4 (forming certificates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.forming_certificates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.forming_certificates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_certificates : Regular.Minimal graph.Adj forming ∧ (Finset.univ.filter forming).card=28.

**Theorem 1.5 (independent certificates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.independent_certificates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.independent_certificates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem independent_certificates : DissociationCover.Dissociates graph.Adj independent ∧ (Finset.univ.filter independent).card=26.

**Definition 1.6 (color).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.color`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.color` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def color (v : Fin 48) : Fin 2.

**Theorem 1.7 (local class).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.local_class`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.local_class` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem local_class : (∀ v w : Fin 48, graph.Adj v w → color v≠color w) ∧ (∀ v : Fin 48, (neighbors v).Nodup) ∧ (∀ v : Fin 48, (neighbors v).length=if v=16 ∨ v=17 then 2 else 3).

**Theorem 1.8 (interface states).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.interface_states`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.interface_states` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem interface_states : ¬ forming 16 ∧ ¬ forming 17 ∧ independent 16 ∧ ¬ independent 17 ∧ color 16=0 ∧ color 17=1.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.color`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.forming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.forming_certificates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.independent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.independent_certificates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.interface_states`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/TripleWitnesses.local_class`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/TripleModule](TripleModule.md)
