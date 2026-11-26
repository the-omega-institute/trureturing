# The actual long-core family and exact beta

## Abstract

The actual long-core family and exact beta

The H and X seams both cross the index permutation. Actual core restriction and three distinct saturated Heawood charges use the exact long-core omission theorem. The original separated word, with compatible seven/eight-block selections, attains beta thirty-three k plus floor(k/2) for every cyclic length. The actual graphs are cubic bipartite and the original thirty-six-per-cell selection is minimal. This module does not yet prove the separate all-k SF upper bound, which is resolved in the written block-compensation source.

**Definition 1.1 (localNeighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.localNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.localNeighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def localNeighbors (v : Fin 62) : List (Fin 62).

**Definition 1.2 (localGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.localGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.localGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def localGraph : SimpleGraph (Fin 62).

**Theorem 1.3 (saturated omission).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.saturated_omission`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.saturated_omission` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem saturated_omission (D : Finset (Fin 62)) (hD : IsKIndependent localGraph 2 D) (j : Fin 3) (h8 : (blockSlice D j).card=8) : evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D.

**Theorem 1.4 (module credit).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.module_credit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.module_credit` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem module_credit (D : Finset (Fin 62)) (hD : IsKIndependent localGraph 2 D) : D.card≤21+(coreSlice D).card+LongCoreOmission.omitted (coreSlice D) false.

**Definition 1.5 (forward).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.forward`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.forward` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def forward (v w : Fin 62) : Prop.

**Definition 1.6 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (e : Equiv.Perm I) : SimpleGraph (I × Fin 62).

**Definition 1.7 (slice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.slice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.slice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def slice (S : Finset (I × Fin 62)) (i : I) : Finset (Fin 62).

**Definition 1.8 (coreSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.coreSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.coreSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def coreSet (S : Finset (I × Fin 62)) : Finset (I × Fin 20).

**Theorem 1.9 (beta upper).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.beta_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.beta_upper` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_upper (e : Equiv.Perm I) : beta (graph e) 2≤33*Fintype.card I+Fintype.card I/2.

**Definition 1.10 (pattern).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.pattern`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.pattern` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pattern (kind : Bool) : Finset (Fin 62).

**Definition 1.11 (selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.selection`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.selection` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selection (word : I → Bool) : Finset (I × Fin 62).

**Theorem 1.12 (selection independent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.selection_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.selection_independent` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection_independent (e : Equiv.Perm I) (word : I → Bool) (hsep : ∀ i, ¬ (word i=true ∧ word (e i)=true)) : IsKIndependent (graph e) 2 (selection word).

**Theorem 1.13 (cyclic beta).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.cyclic_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.cyclic_beta` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cyclic_beta (k : ℕ) : beta (graph (finRotate k)) 2=33*k+k/2.

**Definition 1.14 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (e : Equiv.Perm I) (v : I × Fin 62) : List (I × Fin 62).

**Theorem 1.15 (regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular (e : Equiv.Perm I) : ∀ v, DegreeCapacity.degree (graph e) v=3.

**Theorem 1.16 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (e : Equiv.Perm I) : (graph e).Colorable 2.

**Theorem 1.17 (forming minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.forming_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.forming_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_minimal (e : Equiv.Perm I) : Regular.Minimal (graph e).Adj (fun v => ClosedRingWitnesses.forming v.2).

**Theorem 1.18 (sf lower).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.sf_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.sf_lower` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_lower (e : Equiv.Perm I) : 36*Fintype.card I≤SF (graph e) 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.beta_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.coreSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.cyclic_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.forming_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.forward`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.localGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.localNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.module_credit`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.pattern`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.saturated_omission`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.selection_independent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.sf_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.slice`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses](ClosedRingWitnesses.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission](LongCoreOmission.md)
