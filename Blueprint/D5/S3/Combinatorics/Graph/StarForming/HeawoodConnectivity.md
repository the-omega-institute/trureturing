# Reciprocal interfaces preserve two-connectivity

## Abstract

Reciprocal interfaces preserve two-connectivity

The actual broken Heawood block stays connected after any vertex deletion. Reciprocal opposite-port edges lift every preconnected loopless interaction graph to a graph connected before and after each vertex deletion, with order at least three for a nonempty finite index type. The actual loop-aware independence maximum reduces to the ordinary independent-set maximum, giving exact SF and beta. Degree, cyclic girth and nonplanarity are separate assertions.

**Theorem 1.1 (broken delete preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.broken_delete_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.broken_delete_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem broken_delete_preconnected (z : Fin 14) : (HeawoodPorts.graph.induce {a | a ≠ z}).Preconnected.

**Theorem 1.2 (broken preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.broken_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.broken_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem broken_preconnected : HeawoodPorts.graph.Preconnected.

**Definition 1.3 (reciprocal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def reciprocal {I : Type} (Q : SimpleGraph I) : SimpleGraph (I × Fin 2).

**Theorem 1.4 (reciprocal bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem reciprocal_bipartite {I : Type} [Fintype I] [DecidableEq I] (Q : SimpleGraph I) : (graph (reciprocal Q)).Colorable 2.

**Theorem 1.5 (reciprocal delete preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_delete_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_delete_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem reciprocal_delete_preconnected {I : Type} (Q : SimpleGraph I) (hQ : Q.Preconnected) (z : I × Fin 14) : ((graph (reciprocal Q)).induce {x | x ≠ z}).Preconnected.

**Theorem 1.6 (reciprocal preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem reciprocal_preconnected {I : Type} (Q : SimpleGraph I) (hQ : Q.Preconnected) : (graph (reciprocal Q)).Preconnected.

**Theorem 1.7 (reciprocal two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem reciprocal_two_connected {I : Type} [Fintype I] [Nonempty I] (Q : SimpleGraph I) (hQ : Q.Preconnected) : (graph (reciprocal Q)).Connected ∧ (∀ z : I × Fin 14, ((graph (reciprocal Q)).induce {x | x ≠ z}).Connected) ∧ 3 ≤ Fintype.card (I × Fin 14).

**Theorem 1.8 (reciprocal interaction).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_interaction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_interaction` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem reciprocal_interaction {I : Type} [Fintype I] [DecidableEq I] (Q : SimpleGraph I) (i j : I) : interaction (reciprocal Q) i j ↔ Q.Adj i j.

**Theorem 1.9 (reciprocal alpha0).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_alpha0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_alpha0` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem reciprocal_alpha0 {I : Type} [Fintype I] [DecidableEq I] (Q : SimpleGraph I) : alpha0 (reciprocal Q) = Q.indepNum.

**Theorem 1.10 (reciprocal sf beta).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_sf_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_sf_beta` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem reciprocal_sf_beta {I : Type} [Fintype I] [DecidableEq I] (Q : SimpleGraph I) : StarFormingDissociationRefutation.SF (graph (reciprocal Q)) 2 = 8*Fintype.card I ∧ StarFormingDissociationRefutation.beta (graph (reciprocal Q)) 2 = 7*Fintype.card I + Q.indepNum.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.broken_delete_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.broken_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_alpha0`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_delete_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_interaction`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_sf_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodConnectivity.reciprocal_two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity](FiberConnectivity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces](HeawoodInterfaces.md)
