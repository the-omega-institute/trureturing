# Connected canonical countercovers and exact triangle scope

## Abstract

Connected canonical countercovers and exact triangle scope

For a connected simple base graph with a minimal forming selection, a selected vertex lacking a safe certificate has an actual fragile triangle. Exactly one crossed edge in the canonical two-sheeted graph joins its root sheets. Actual base-path lifting and the sheet flip prove connectivity, and the original missing-certificate theorem proves nonminimality of the full pullback. Thus connected two-sheeted tests detect the same failure. The selected pair in the complete triangle has safe self-failures despite violating boundary triangle-freeness. The explicit connected seven-vertex triangle example is minimal but has a connected canonical double cover with nonminimal full pullback. No finite base-order restriction or global surjectivity assumption is introduced.

**Definition 1.1 (canonicalGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.canonicalGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.canonicalGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def canonicalGraph : SimpleGraph (V × Bool).

**Theorem 1.2 (canonical preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.canonical_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.canonical_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem canonical_preconnected (hG : G.Preconnected) (hS : Minimal G.Adj S) (hd : S d) (hmissing : ¬ ((¬ TwoAt G.Adj (fun v => S v ∧ v≠d) d) ∨ ∃ outside, SafeFailure G.Adj S d outside)) : (canonicalGraph G S d).Preconnected.

**Theorem 1.3 (connected countercover).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.connected_countercover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.connected_countercover` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem connected_countercover (hG : G.Preconnected) (hS : Minimal G.Adj S) (hd : S d) (hmissing : ¬ ((¬ TwoAt G.Adj (fun v => S v ∧ v≠d) d) ∨ ∃ outside, SafeFailure G.Adj S d outside)) : (canonicalGraph G S d).Preconnected ∧ NeighborhoodCover G.Adj (canonicalGraph G S d).Adj Prod.fst ∧ ¬ Minimal (canonicalGraph G S d).Adj (fun v => S v.1).

**Theorem 1.4 (safe iff connected covers).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.safe_iff_connected_covers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.safe_iff_connected_covers` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem safe_iff_connected_covers (hG : G.Preconnected) (hS : Minimal G.Adj S) : HasSafeCertificates G.Adj S ↔ ∀ H : SimpleGraph (V × Bool), NeighborhoodCover G.Adj H.Adj Prod.fst → H.Preconnected → Minimal H.Adj (fun v => S v.1).

**Theorem 1.5 (triangle scope).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.triangle_scope`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.triangle_scope` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem triangle_scope : let A : Fin 3 → Fin 3 → Prop.

**Definition 1.6 (sevenNeighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.sevenNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.sevenNeighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sevenNeighbors (v : Fin 7) : List (Fin 7).

**Definition 1.7 (sevenGraph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.sevenGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.sevenGraph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sevenGraph : SimpleGraph (Fin 7).

**Definition 1.8 (sevenSelected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.sevenSelected`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.sevenSelected` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sevenSelected (v : Fin 7) : Prop.

**Theorem 1.9 (seven counterexample).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.seven_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.seven_counterexample` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem seven_counterexample : Minimal sevenGraph.Adj sevenSelected ∧ sevenGraph.Preconnected ∧ (canonicalGraph sevenGraph sevenSelected 0).Preconnected ∧ NeighborhoodCover sevenGraph.Adj (canonicalGraph sevenGraph sevenSelected 0).Adj Prod.fst ∧ ¬Minimal (canonicalGraph sevenGraph sevenSelected 0).Adj (fun v => sevenSelected v.1).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.canonicalGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.canonical_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.connected_countercover`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.safe_iff_connected_covers`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.sevenGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.sevenNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.sevenSelected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.seven_counterexample`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity.triangle_scope`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CoverStability](CoverStability.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteCover](FiniteCover.md)
