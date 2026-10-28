# Refuting the unrestricted Conjecture 2

## Abstract

The full finite-graph Conjecture 2 of Boyer--Kuenzel--Lyle--Pellico is false.

**Definition 1.1 (Conjecture 2 in its complete quantified form).**

$$\mathrm{claim}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition retains every finite simple graph and positive integer k. Its left side includes connectedness, the all-j maximal induced proper-coloring well-hued condition, the sequence (alpha,2 alpha,...,k alpha), and chromatic number k. Its right side is a spanning subgraph of a balanced complete k-partite host together with the induced closed-anti-neighborhood exclusion.

**Theorem 1.2 (The 3 by 3 rook graph counterexample).**

$$\neg \mathrm{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/boyer-kuenzel-lyle-pellico-2025-conjecture-two` (refuted) by `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"boyer-kuenzel-lyle-pellico-2025-conjecture-two","declaration_gid":"D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The graph on Fin 3 times Fin 3 joins distinct cells in a common row or column. Its independence number is three and its balanced three-color partition satisfies the right side. The displayed five-cell C4 plus isolated vertex and six-cell C6 are inclusion-maximal induced bipartite sets, of unequal orders five and six. Therefore the graph is not well-hued while the right side holds.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation.result`
