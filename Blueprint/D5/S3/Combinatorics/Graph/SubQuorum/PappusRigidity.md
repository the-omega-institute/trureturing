# Pappus representative and coloring rigidity

## Abstract

Pappus representative and coloring rigidity

A feasible singleton and matching pair of total size ten has an empty matching. Every ten-color Pappus sub-quorum coloring has a ten-vertex dissociation support and is injective on that support.

**Theorem 1.1 (pappus optimal matching empty).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/PappusRigidity.pappus_optimal_matching_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/PappusRigidity.pappus_optimal_matching_empty` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_optimal_matching_empty (T : Finset (Fin 18)) (M : Finset (Fin 18 × Fin 18)) (hf : Feasible pappusGraph T M) (hc : T.card + M.card = 10) : M = ∅.

**Theorem 1.2 (pappus coloring rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/PappusRigidity.pappus_coloring_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/PappusRigidity.pappus_coloring_rigidity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_coloring_rigidity (c : Fin 18 → Option ℕ) (hc : IsSubQuorum pappusGraph c) (hp : (palette c Finset.univ).card = 10) : IsKIndependent pappusGraph 2 (coloredSupport c Finset.univ) ∧ (coloredSupport c Finset.univ).card = 10 ∧ Set.InjOn c (coloredSupport c Finset.univ).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/PappusRigidity.pappus_coloring_rigidity`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/PappusRigidity.pappus_optimal_matching_empty`
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives](C4FreeRepresentatives.md)
