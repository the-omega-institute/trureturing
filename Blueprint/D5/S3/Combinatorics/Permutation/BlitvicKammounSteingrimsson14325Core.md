# Exact source structure of 14325 packings

## Abstract

The prescribed 14325 permutations have the exact transfer count and both universal modular laws.

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

**Theorem 1.4 (The actual grid cardinality is the transfer row).**

$$\forall j: \mathbb{N}, (1 \leq j) \implies card\left(GridPacking\left(j\right)\right) = rowNat\left(j - 1, 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.grid_card_eq_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

For every natural j≥1, the grid cardinality equals row ℕ (j−1) 3. For a grid q of N=3j ranks let d be the rank of its last x, and k=N−d. Appending a column inserts its z as the new greatest rank. Choose 0≤r<k and 0≤s≤r, insert y at rank b=N−r+s, then x at rank a=N−r. The old ranks are embedded by the two ordered succAbove maps. Exactly the conditions d<a≤b≤N preserve every old and new column and horizontal comparison. The new state is r+3. Conversely, every grid has its last z at the greatest rank; deleting the last x, y and z recovers a unique old grid and the unique choices r=N−a and s=b−a. Thus childrenEquiv is a bijection from the actual grids with their finite insertion choices, with no quotient or labeling factor. Summing row ℕ n over the actual grid states changes, under this bijection, into row ℕ (n+1) over the parent states. The unique one-column grid has state three; induction on the number of columns proves the claimed cardinality. The recurrence is derived from actual permutations, never assumed.

**Theorem 1.5 (Exact modulo-ten law for actual permutations).**

$$\forall j: \mathbb{N}, (1 \leq j) \implies mod\left(count\left(pattern, 2, j\right), 10\right) = dyadicResidue\left(j + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_mod_ten` (`✓ std3`). ∎

*Resolves.* `Problems/bks11-14325-whole-event` (proved) by `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_mod_ten` and `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_mod_four_iff`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bks11-14325-whole-event","declaration_gid":"D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_mod_ten","resolution_kind":"proved"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bks11-14325-whole-event","declaration_gid":"D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_mod_four_iff","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

For every j≥1 the actual count is one modulo ten precisely on j+1=2ᵏ with k≥1, and six otherwise. Here dyadicResidue(m) means one on that existential condition and six off it. Compose count_eq_grid with grid_card_eq_row and apply row_mod_ten, using (j−1)+2=j+1. All prescribed windows and all comparisons retain their literal source interpretation; extra occurrences are allowed.

**Theorem 1.6 (Exact four-divisibility exceptions for actual permutations).**

$$\forall j: \mathbb{N}, (1 \leq j) \implies fourNondivides\left(count\left(pattern, 2, j\right)\right) \iff \exists i,p: \mathbb{N}, p \leq i \land j + 1 = 2^{i} + 2^{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_mod_four_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

For every j≥1, four does not divide the actual count if and only if j+1=2ⁱ+2ᵖ for natural exponents p≤i. The proof uses the same actual-count correspondence and row_mod_four_iff. Both implications, p=0 and p=i are retained. There is no assertion for j=0. The printed item says four divides all but these indices and does not explicitly assert the converse; this iff proves the stronger registered exact interpretation.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_eq_grid`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_mod_four_iff`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.count_mod_ten`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.grid_card_eq_row`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.packing_bounds`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.packing_extrema`
- Dependency: [D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer](BlitvicKammounSteingrimsson14325Transfer.md)
- Dependency: [D5/S3/Combinatorics/Permutation/PackingMaximumRefutation](PackingMaximumRefutation.md)
