# All-length two-connectivity of the actual long-core assembly

## Abstract

All-length two-connectivity of the actual long-core assembly

The open sixty-two-vertex local module retains actual vertex-deletion paths. The H5-to-next-H0 bridge and symbolic transitive permutation give two-connectivity at every positive cyclic length, including one and two. This is the source long-core graph with both crossing seams and is distinct from the closed-high Z family.

**Theorem 1.1 (two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreConnectivity.two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreConnectivity.two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_connected [Nonempty I] (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j) : (graph e).Connected ∧ (∀ z : I × Fin 62, ((graph e).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (I × Fin 62).

**Theorem 1.2 (cyclic two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreConnectivity.cyclic_two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreConnectivity.cyclic_two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_two_connected (r : ℕ) (hr : 0<r) : (graph (finRotate r)).Connected ∧ (∀ z : Fin r × Fin 62, ((graph (finRotate r)).induce {x | x≠z}).Connected) ∧ 3≤Fintype.card (Fin r × Fin 62).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreConnectivity.cyclic_two_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreConnectivity.two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity](CyclicConnectivity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/LongCoreRings](LongCoreRings.md)
