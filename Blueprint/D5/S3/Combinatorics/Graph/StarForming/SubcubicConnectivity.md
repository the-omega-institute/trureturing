# All-size two-connectivity of actual shared ports

## Abstract

All-size two-connectivity of actual shared ports

The actual ten-vertex core has local vertex-deletion path certificates. An arbitrary transitive index permutation gives paths after deletion through forward or backward shared-port bridges. Every positive cyclic size is covered; the separate bipartite parameter theorem requires even r.

**Theorem 1.1 (delete preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.delete_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.delete_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem delete_preconnected (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) (z : I × Fin 11) : ((graph e).induce {x | x≠z}).Preconnected.

**Theorem 1.2 (preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem preconnected (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Preconnected.

**Theorem 1.3 (two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 11, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 11).

**Theorem 1.4 (cyclic two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.cyclic_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.cyclic_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 11, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 11).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.cyclic_two_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.delete_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicConnectivity.two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity](FiberConnectivity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification](SubcubicIdentification.md)
