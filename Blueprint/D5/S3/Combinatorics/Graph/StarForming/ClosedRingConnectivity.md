# Two-connectivity of all cyclic closed-high assemblies

## Abstract

Two-connectivity of all cyclic closed-high assemblies

A finite local parent/rank certificate for the sixty-two-vertex open module is combined with a symbolic arbitrary transitive-permutation orbit argument. Every vertex-deleted graph stays connected. The cyclic specialization covers every positive size, including one and two. Neither connectivity nor the parameter equalities are inferred from a finite list of ring sizes.

**Theorem 1.1 (module delete preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.module_delete_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.module_delete_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem module_delete_preconnected (z : Fin 62) : (ClosedModule.graph.induce {a | a≠z}).Preconnected.

**Theorem 1.2 (delete preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.delete_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.delete_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem delete_preconnected (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (z : I × Fin 62) : ((graph e).induce {x | x≠z}).Preconnected.

**Theorem 1.3 (preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem preconnected (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Preconnected.

**Theorem 1.4 (two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 62, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 62).

**Theorem 1.5 (cyclic two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.cyclic_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.cyclic_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 62, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 62).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.cyclic_two_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.delete_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.module_delete_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedRingConnectivity.two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClosedRings](ClosedRings.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity](FiberConnectivity.md)
