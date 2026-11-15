# Actual higher-cover density through connected double quotients

## Abstract

Actual higher-cover density through connected double quotients

An arbitrary neighborhood cover of the actual binary Heawood base with two-element fibers is the intermediate graph. Its actual connectedness gives a dissociation set of size at least fifteen. Exact finite fiber cardinalities and actual cubic bipartite parameter transport prove fifteen times the higher-cover order at most twenty-eight beta and one hundred ninety-six times its SF-minus-beta gap at most nine times its order. Zero higher fibers are included. No deck-group factorization, character injection or rank-four matrix-space extraction is assumed to have been completed.

**Theorem 1.1 (connected double quotient).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodHigherCovers.connected_double_quotient`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodHigherCovers.connected_double_quotient` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem connected_double_quotient (p : V → Fin 14) (double : CoverPullback.NeighborhoodCover HeawoodLift.base.Adj Q.Adj p) (two : ∀ v, (Finset.univ.filter (fun x => p x=v)).card=2) (connected : Q.Preconnected) (q : W → V) (higher : CoverPullback.NeighborhoodCover Q.Adj H.Adj q) (k : ℕ) (fibers : ∀ v, (Finset.univ.filter (fun x => q x=v)).card=k) : 15*Fintype.card W ≤ 28*beta H 2 ∧ 196*(SF H 2-beta H 2) ≤ 9*Fintype.card W.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodHigherCovers.connected_double_quotient`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodAllDoubleCovers](HeawoodAllDoubleCovers.md)
