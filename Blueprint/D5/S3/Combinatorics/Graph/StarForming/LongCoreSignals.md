# All-length zero-block-loss direct-signal obstruction

## Abstract

All-length zero-block-loss direct-signal obstruction

The source thirty-four-set and complete deletion-failure table are checked in the actual one-cell long-core graph. Folding module labels is an actual neighborhood bijection for every finite module permutation. Triangle-free cover pullback proves minimality of the repeated selection. Exact fiber counts give thirty-four vertices per module, ten selected core vertices per module, and eight in every attached block. Each omitted opposite core root has its unique selected signal port as selected neighbor, while that port has two selected internal neighbors. Thus these actual signals coexist with zero block deficit. This is an obstruction to assigning a positive block loss per signal; it does not refute the solved written thirty-six-per-module upper bound.

**Definition 1.1 (baseGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.baseGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.baseGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def baseGraph : SimpleGraph (Fin 62).

**Theorem 1.2 (cover).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.cover` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem cover (e : Equiv.Perm I) : CoverPullback.NeighborhoodCover baseGraph.Adj (graph e).Adj Prod.snd.

**Definition 1.3 (chosen).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.chosen`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.chosen` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def chosen (v : Fin 62) : Prop.

**Definition 1.4 (failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.failure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.failure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def failure (v : Fin 62) : Fin 62.

**Theorem 1.5 (minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal (e : Equiv.Perm I) : Regular.Minimal (graph e).Adj (fun v => chosen v.2).

**Definition 1.6 (selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.selection`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.selection` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selection : Finset (I × Fin 62).

**Theorem 1.7 (counts).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.counts` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem counts : (selection (I.

**Theorem 1.8 (direct signals).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.direct_signals`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.direct_signals` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem direct_signals (e : Equiv.Perm I) (i : I) : (i,(13 : Fin 62))∉selection ∧ (i,(20 : Fin 62))∈selection ∧ (graph e).Adj (i,13) (i,20) ∧ (∀ v, v∈selection → (graph e).Adj (i,13) v → v=(i,20)) ∧ (i,(27 : Fin 62))∈selection ∧ (i,(30 : Fin 62))∈selection ∧ (graph e).Adj (i,20) (i,27) ∧ (graph e).Adj (i,20) (i,30).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.baseGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.chosen`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.counts`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.cover`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.direct_signals`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/LongCoreSignals.selection`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CoverPullback](CoverPullback.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/LongCoreRings](LongCoreRings.md)
