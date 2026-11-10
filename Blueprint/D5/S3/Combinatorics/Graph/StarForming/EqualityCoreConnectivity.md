# All-length equality-core two-connectivity

## Abstract

All-length equality-core two-connectivity

Actual local vertex-deletion paths of the twenty-vertex open core and the high-cycle seam give connectivity and one-vertex-deletion connectivity for every transitive finite index permutation. The positive cyclic specialization includes length one. No finite list of core sizes substitutes for this arbitrary-orbit proof.

**Theorem 1.1 (two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCoreConnectivity.two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCoreConnectivity.two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 20, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 20).

**Theorem 1.2 (cyclic two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCoreConnectivity.cyclic_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCoreConnectivity.cyclic_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 20, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 20).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCoreConnectivity.cyclic_two_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCoreConnectivity.two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity](CyclicConnectivity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/EqualityCore](EqualityCore.md)
