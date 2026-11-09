# Exact source structure of 14325 packings

## Abstract

The prescribed 14325 comparisons force the first and last ranks for every positive packing size.

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

The remaining grid has xₜ=aₜ₊₁<yₜ=cₜ<zₜ=bₜ, with increasing x and z chains. An exact rank-assignment/grid bijection and first-z insertion/deletion bijection are still required to identify the actual cardinality with the transfer rows. The present theorems prove endpoint constraints and do not claim that cardinality identity, either modular conclusion, or completion of issue 28504.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.packing_bounds`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.packing_extrema`
- Dependency: [D5/S3/Combinatorics/Permutation/PackingMaximumRefutation](PackingMaximumRefutation.md)
