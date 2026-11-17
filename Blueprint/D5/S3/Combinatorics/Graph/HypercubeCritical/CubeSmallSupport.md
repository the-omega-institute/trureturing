# A singleton neighbor for a small actual cube set

## Abstract

Every nonempty set of at most six cube vertices in dimension at least nine has a singleton neighbor.

This combinatorial ingredient serves the Q9 energy and cut bounds. The original question whether f₂(Q₉)=3 or 4 remains unresolved; the 48- and 96-vertex bounds do not exclude a 258-vertex candidate.

**Theorem 1.1 (A vertex with exactly one selected cube neighbor).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport.exists_unique_neighbor_of_card_le_six`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport.exists_unique_neighbor_of_card_le_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 9 ≤ n and a nonempty S : Finset (Q n) with S.card ≤ 6, there exists y : Q n such that (S.filter (fun x => (hypercube n).Adj y x)).card = 1. Adjacency is the actual Boolean cube adjacency. There is no parity, signing or star-structure hypothesis.

If no singleton neighbor exists, the two-coordinate differences from any selected root cover every direction. Omitting any other selected vertex leaves at most four such pairs, so all distinct selected vertices must be at Hamming distance two. Fix one difference pair A. Every other difference contributes at most one coordinate outside A, giving at most 2 + 5 = 7 covered directions, contrary to 9 ≤ n.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport.exists_unique_neighbor_of_card_le_six`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](BalancedCriticalSpectrum.md)
