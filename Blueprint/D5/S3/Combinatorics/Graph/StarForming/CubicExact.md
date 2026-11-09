# Arbitrary ambient broken-Heawood block cap

## Abstract

Arbitrary ambient broken-Heawood block cap

An injective ambient embedding preserves all broken-Heawood edges, and every nonport has exactly its stated internal neighborhood. With those hypotheses, the dense local deletion certificate implies that every ambient inclusion-minimal selection has at most eight vertices in this block. Ports zero and eight remain distinct and may have outside neighbors. No cyclic charge or independent-set formula for an arbitrary interaction graph is inferred here.

**Theorem 1.1 (lift broken star).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicExact.lift_broken_star`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicExact.lift_broken_star` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem lift_broken_star {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 14 → Vertex) (mask : Fin 16384) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hsound : ∀ first second, BrokenAdj first second → adjacency (embedding first) (embedding second)) (hselection : ∀ vertex, selection (embedding vertex) ↔ chosen mask.val vertex = true) (deleted outside : Fin 14) (hstar : TwoAt BrokenAdj (fun vertex => chosen mask.val vertex = true ∧ vertex ≠ deleted) outside) : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ embedding deleted) (embedding outside).

**Theorem 1.2 (ambient heawood cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicExact.ambient_heawood_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicExact.ambient_heawood_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem ambient_heawood_cap {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (embedding : Fin 14 → Vertex) (mask : Fin 16384) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hinjective : ∀ first second, embedding first = embedding second → first = second) (hsound : ∀ first second, BrokenAdj first second → adjacency (embedding first) (embedding second)) (hselection : ∀ vertex, selection (embedding vertex) ↔ chosen mask.val vertex = true) (hnonport : ∀ vertex, vertex ≠ 0 → vertex ≠ 8 → ∀ outside, adjacency (embedding vertex) outside → ∃ other, outside = embedding other ∧ BrokenAdj vertex other) (hminimal : Minimal adjacency selection) : selectedCard mask.val ≤ 8.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicExact.ambient_heawood_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicExact.lift_broken_star`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CubicDense](CubicDense.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicExact](SubcubicExact.md)
