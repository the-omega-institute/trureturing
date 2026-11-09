# Exact source structure of 14325 packings

## Abstract

The prescribed 14325 permutations correspond exactly to rank assignments on the endpoint-deleted grid.

The zero-based pattern is (0,3,2,1,4), overlap is two, and stride is three. The source length 5+(j−1)·3 equals 3j+2 for j≥1. Packs is the existing predicate requiring every strict pairwise comparison in every prescribed window. There is no avoidance condition or quotient, and extra occurrences are allowed.

Write aₜ for position 3t, bₜ for position 3t+1, and cₜ for position 3t+2. Window t requires precisely aₜ<aₜ₊₁<cₜ<bₜ<bₜ₊₁. The private packing_chain_iff proves both directions of this comparison translation. The private chain_bounds then proves by induction on the number of windows that every position lies between a₀ and bⱼ in rank.

**Theorem 1.1 (Bounds for every rank assignment).**

$$\forall j: \mathbb{N}, (1 \leq j) \implies \forall w: Fin\left(5 + \left(j - 1\right) \cdot 3\right) \to Fin\left(5 + \left(j - 1\right) \cdot 3\right), (Packs\left(pattern, 2, j, w\right)) \implies \forall x: Fin\left(5 + \left(j - 1\right) \cdot 3\right), (w\left(0\right) \leq w\left(x\right)) \land (w\left(x\right) \leq w\left(3 \cdot j + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.packing_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

For every natural j≥1, every rank function w satisfying Packs, and every position x, w(0)≤w(x)≤w(3j+1). Injectivity is not required. Appending a window adds three positions, and its chain orders all three between the old lower endpoint and the new upper endpoint.

**Theorem 1.2 (Forced ranks in actual source permutations).**

$$\forall j: \mathbb{N}, (1 \leq j) \implies \forall w: Perm\left(Fin\left(5 + \left(j - 1\right) \cdot 3\right)\right), (Packs\left(pattern, 2, j, w\right)) \implies (w\left(0\right) = 0) \land (w\left(3 \cdot j + 1\right) = 3 \cdot j + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.packing_extrema` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

For every natural j≥1 and every actual permutation w satisfying Packs, w(0)=0 and w(3j+1)=3j+1. Surjectivity supplies a position with rank zero and one with the greatest rank; packing_bounds forces the two endpoint equalities. Thus deleting these endpoints removes two forced ranks, without any symmetry or labeling factor.

**Theorem 1.3 (Exact cardinality after removing endpoints).**

$$\forall j: \mathbb{N}, (1 \leq j) \implies count\left(pattern, 2, j\right) = card\left(GridPacking\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_eq_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

For every natural j≥1, the actual count equals the number of grid rank assignments. GridPacking consists of permutations q of 3j ranks, indexed so that q(3t+2), q(3t+1), q(3t) are xₜ, yₜ, zₜ. Each column satisfies xₜ<yₜ<zₜ, and both x and z increase across successive columns. The map packingGridEquiv removes positions 0 and 3j+1 and subtracts one from each remaining rank. Its inverse adds one to every grid rank and inserts the forced ranks 0 and 3j+1. The column and horizontal inequalities recover all four comparisons of every window, including the first and last windows. The two maps are inverse on actual permutations, so no labeling or symmetry factor occurs.

A first-z insertion/deletion bijection is still required to identify this grid cardinality with the transfer rows. Neither modular conclusion for the actual count follows from the endpoint-deletion equality alone.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_eq_grid`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.packing_bounds`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.packing_extrema`
- Dependency: [D5/S3/Combinatorics/Permutation/PackingMaximumRefutation](PackingMaximumRefutation.md)
