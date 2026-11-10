# Actual arbitrary-ambient bare-port Heawood loss

## Abstract

Actual arbitrary-ambient bare-port Heawood loss

Every selection of the fixed fourteen-vertex broken Heawood block is checked by a complete Boolean certificate. Selections exceeding the exact selected-cardinality plus bare-port budget have an actually safe nonport deletion. The original supported-deletion argument transports this to every actual ambient finite graph with a faithful block embedding and exact nonport neighborhoods. The result counts the two actual bare ports separately and proves cardinality plus bare-port count at most eight. Internal block formation is not assumed. This does not assert the full imported-charge or global block-compensation theorem.

**Definition 1.1 (bareBool).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.bareBool`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.bareBool` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def bareBool (mask : ℕ) (port : Fin 14) : Bool.

**Definition 1.2 (bareCount).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.bareCount`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.bareCount` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def bareCount (mask : ℕ) : ℕ.

**Theorem 1.3 (ambient bare cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.ambient_bare_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.ambient_bare_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem ambient_bare_cap {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 14 → Vertex) (mask : Fin 16384) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hsound : ∀ first second, BrokenAdj first second → adjacency (embedding first) (embedding second)) (hselection : ∀ vertex, selection (embedding vertex) ↔ chosen mask.val vertex = true) (hnonport : ∀ vertex, vertex ≠ 0 → vertex ≠ 8 → ∀ outside, adjacency (embedding vertex) outside → ∃ other, outside = embedding other ∧ BrokenAdj vertex other) (hminimal : Minimal adjacency selection) : selectedCard mask.val+bareCount mask.val ≤ 8.

**Theorem 1.4 (bareCount eq).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.bareCount_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.bareCount_eq` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bareCount_eq (C : Finset (Fin 14)) (mask : Fin 16384) (hmask : ∀ v, chosen mask.val v=true ↔ v ∈ C) : bareCount mask.val=(barePorts C).card.

**Theorem 1.5 (ambient graph bare cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.ambient_graph_bare_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.ambient_graph_bare_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem ambient_graph_bare_cap {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (embedding : Fin 14 → V) (hinjective : Function.Injective embedding) (hsound : ∀ a b, BrokenAdj a b → G.Adj (embedding a) (embedding b)) (hnonport : ∀ v, v≠0 → v≠8 → ∀ x, G.Adj (embedding v) x → ∃ w, x=embedding w ∧ BrokenAdj v w) (hminimal : StarFormingDissociationRefutation.IsMinimalStarForming G 2 S) : let C.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.ambient_bare_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.ambient_graph_bare_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.bareBool`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.bareCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap.bareCount_eq`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CubicExact](CubicExact.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteCover](FiniteCover.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteMasks](FiniteMasks.md)
