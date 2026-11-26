# Actual shared-port subcubic assemblies

## Abstract

Actual shared-port subcubic assemblies

The actual vertex type has ten core vertices and one identified port per cell. Source port zero maps to the current port and source port six to the next port. Degrees and the ambient-core upper bound concern this graph, with each port counted once. The explicit seven-per-cell minimal selection attains SF. Even-cycle dissociation, structural and other graph invariants require their own proofs.

**Definition 1.1 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (next : Equiv.Perm I) (x : I × Fin 11) : List (I × Fin 11).

**Definition 1.2 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (next : Equiv.Perm I) : SimpleGraph (I × Fin 11).

**Theorem 1.3 (degrees).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.degrees` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem degrees (next : Equiv.Perm I) (i : I) (v : Fin 11) : DegreeCapacity.degree (graph next) (i,v)= if v=3 ∨ v=4 ∨ v=6 ∨ v=7 ∨ v=10 then 2 else 3.

**Definition 1.4 (core).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.core`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.core` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def core (i : I) (v : Fin 10) : I × Fin 11.

**Definition 1.5 (port).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.port`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.port` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def port (i : I) : I × Fin 11.

**Definition 1.6 (coreSlice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.coreSlice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.coreSlice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def coreSlice (S : Finset (I × Fin 11)) (i : I) : Finset (Fin 10).

**Definition 1.7 (slice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.slice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.slice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def slice (S : Finset (I × Fin 11)) (i : I) : Finset (Fin 11).

**Theorem 1.8 (core edges).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.core_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.core_edges` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem core_edges (next : Equiv.Perm I) (i : I) (v w : Fin 10) : (graph next).Adj (core i v) (core i w) ↔ Subcubic.CoreAdj v w.

**Theorem 1.9 (card slice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.card_slice`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.card_slice` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem card_slice (S : Finset (I × Fin 11)) (i : I) : (slice S i).card=(coreSlice S i).card+(if port i∈S then 1 else 0).

**Theorem 1.10 (sf upper).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.sf_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.sf_upper` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_upper (next : Equiv.Perm I) : SF (graph next) 2≤7*Fintype.card I.

**Definition 1.11 (forming).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.forming`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.forming` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def forming (x : I × Fin 11) : Prop.

**Definition 1.12 (failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.failure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.failure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def failure (x : I × Fin 11) : I × Fin 11.

**Theorem 1.13 (forming minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.forming_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.forming_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_minimal (next : Equiv.Perm I) : IsMinimalStarForming (graph next) 2 (Finset.univ.filter forming).

**Theorem 1.14 (sf exact).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.sf_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.sf_exact` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_exact (next : Equiv.Perm I) : SF (graph next) 2=7*Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.card_slice`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.core`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.coreSlice`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.core_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.degrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.forming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.forming_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.port`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.sf_exact`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.sf_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification.slice`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClosedModule](ClosedModule.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicExact](SubcubicExact.md)
