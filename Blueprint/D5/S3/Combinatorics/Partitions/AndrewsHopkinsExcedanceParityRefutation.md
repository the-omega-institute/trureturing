# A counterexample to excedance parity positivity

## Abstract

The original one-based excedance statistic gives more odd than even partitions at n = 28.

A partition of n is a finite weakly decreasing list of positive integers with sum n. Nat.Partition n stores its multiset of parts with positivity and sum proofs. Sorting in decreasing order identifies this carrier with the original lists, with every multiplicity retained. An excedance is an index i starting at one for which the ith part is strictly greater than i.

**Definition 1.1 (The decreasing list of parts).**

$$\forall (n: \mathbb{N}), \forall (p: \operatorname{Nat.Partition}\left(n\right)), \operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.decreasingParts}\left(p\right) = \operatorname{Multiset.sort}\left(\operatorname{Nat.Partition.parts}\left(p\right), \lambda (a: \mathbb{N}) \mapsto \lambda (b: \mathbb{N}) \mapsto a \ge b\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.decreasingParts` (`✓ std3`).

*Citation.* George Andrews, Brian Hopkins (2026). *Excedances and Deficiencies of Integer Partitions*. DOI: [10.48550/arXiv.2611.00435](https://doi.org/10.48550/arXiv.2611.00435). URL: <https://arxiv.org/abs/2611.00435v1>.

*Commentary.*

For every natural n and partition p of n, decreasingParts sorts the full multiset of parts in weakly decreasing order. There is no bound on the list length or the size of n.

**Definition 1.2 (One-based excedances).**

$$\forall (n: \mathbb{N}), \forall (p: \operatorname{Nat.Partition}\left(n\right)), \operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.excedances}\left(p\right) = \operatorname{Fintype.card}\left(\{i : \operatorname{Fin}\left(\operatorname{List.length}\left(\operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.decreasingParts}\left(p\right)\right)\right) \mid \operatorname{List.get}\left(\operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.decreasingParts}\left(p\right), i\right) > \operatorname{Fin.val}\left(i\right) + 1\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.excedances` (`✓ std3`).

*Citation.* George Andrews, Brian Hopkins (2026). *Excedances and Deficiencies of Integer Partitions*. DOI: [10.48550/arXiv.2611.00435](https://doi.org/10.48550/arXiv.2611.00435). URL: <https://arxiv.org/abs/2611.00435v1>.

*Commentary.*

The finite index i in Lean starts at zero. Comparing the indexed part with i.val + 1 therefore implements exactly the original one-based inequality. Every index of the decreasing list is considered, including the last index; equality is not an excedance.

**Definition 1.3 (The full even carrier).**

$$\forall (n: \mathbb{N}), \operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.evenCount}\left(n\right) = \operatorname{Fintype.card}\left(\{p : \operatorname{Nat.Partition}\left(n\right) \mid \operatorname{Even}\left(\operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.excedances}\left(p\right)\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.evenCount` (`✓ std3`).

*Citation.* George Andrews, Brian Hopkins (2026). *Excedances and Deficiencies of Integer Partitions*. DOI: [10.48550/arXiv.2611.00435](https://doi.org/10.48550/arXiv.2611.00435). URL: <https://arxiv.org/abs/2611.00435v1>.

*Commentary.*

For every natural n, evenCount is the cardinality of the full subtype of Nat.Partition n on which the original excedance count is even. This is a cardinality of actual partitions, without a generating-function or recurrence definition.

**Definition 1.4 (The full odd carrier).**

$$\forall (n: \mathbb{N}), \operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.oddCount}\left(n\right) = \operatorname{Fintype.card}\left(\{p : \operatorname{Nat.Partition}\left(n\right) \mid \operatorname{Odd}\left(\operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.excedances}\left(p\right)\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.oddCount` (`✓ std3`).

*Citation.* George Andrews, Brian Hopkins (2026). *Excedances and Deficiencies of Integer Partitions*. DOI: [10.48550/arXiv.2611.00435](https://doi.org/10.48550/arXiv.2611.00435). URL: <https://arxiv.org/abs/2611.00435v1>.

*Commentary.*

For every natural n, oddCount is the cardinality of the full subtype of Nat.Partition n on which the same original excedance count is odd.

**Definition 1.5 (The universal positivity assertion).**

$$(\operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.claim}: \operatorname{Prop}) = \forall (n: \mathbb{N}), \left(12 \le n\right) \to \left(\operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.evenCount}\left(n\right) > \operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.oddCount}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.claim` (`✓ std3`).

*Citation.* George Andrews, Brian Hopkins (2026). *Excedances and Deficiencies of Integer Partitions*. DOI: [10.48550/arXiv.2611.00435](https://doi.org/10.48550/arXiv.2611.00435). URL: <https://arxiv.org/abs/2611.00435v1>.

*Commentary.*

The assertion after Corollary 7 and Table 1 in Section 2 quantifies over every natural n at least 12 and asks whether evenCount n is strictly greater than oddCount n. The original statistic and Table 1 fix the even-minus-odd direction despite the inconsistent even/odd labels in the displayed generating functions of Corollary 7.

**Theorem 1.6 (The universal assertion is false).**

$$\neg \operatorname{D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/andrews-hopkins-2026-excedance-parity-positivity` (refuted) by `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"andrews-hopkins-2026-excedance-parity-positivity","declaration_gid":"D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* George Andrews, Brian Hopkins (2026). *Excedances and Deficiencies of Integer Partitions*. DOI: [10.48550/arXiv.2611.00435](https://doi.org/10.48550/arXiv.2611.00435). URL: <https://arxiv.org/abs/2611.00435v1>.

*Commentary.*

At n = 28, the full even subtype has cardinality 1850 and the full odd subtype has cardinality 1868. Their difference is -18. Hence the strict inequality required by the universal assertion fails. The proof enumerates positive decreasing lists with remaining sum, maximum part and fuel, proves completeness and absence of duplicates, and converts them injectively into actual Nat.Partition values. Completeness follows by sorting an arbitrary partition; positivity bounds its length by its sum and each part by n. Finite subtype cardinalities then equal the filtered enumeration cardinalities. The original Fin-indexed excedance function is evaluated on these actual partitions, and the resulting closed counts are checked by kernel reduction. This establishes a counterexample at 28; it makes no assertion of the globally first counterexample or of worldwide priority.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.decreasingParts`
- Truth anchor: `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.evenCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.excedances`
- Truth anchor: `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.oddCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.result`
