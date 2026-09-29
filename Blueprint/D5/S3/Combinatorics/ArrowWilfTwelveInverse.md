# Uniqueness of the First Decorated Description

## Abstract

The first decorated construction is injective, and avoidance gives its required normal form.

**Theorem 1.1 (The initial filler prefix).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.takeWhile_filler_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.takeWhile_filler_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When every entry of b fails P and the next entry a satisfies P, taking entries while P fails from b followed by a and a tail returns b.

**Theorem 1.2 (Uniqueness of filler blocks).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.afterBlocks_injective_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.afterBlocks_injective_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For a fixed skeleton whose entries satisfy P, equally long lists of P-failing filler blocks are equal if their interleavings are equal.

**Theorem 1.3 (Uniqueness with a leading block).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.interleaving_blocks_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.interleaving_blocks_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If two words have the same leading skeleton entry, equal separated interleavings determine their leading filler blocks and all following filler blocks.

**Theorem 1.4 (Every word has an interleaving decomposition).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.exists_afterBlocks_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.exists_afterBlocks_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Each list splits into an initial P-failing block and a skeleton of P-satisfying entries, with one P-failing block after each skeleton entry.

**Theorem 1.5 (Splitting at a singleton block).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.fixedSyntax_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.fixedSyntax_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

FixedSyntax f p yields a prefix of values below f, then f, then either no entry or an entry larger than f followed by a tail.

**Theorem 1.6 (Recovering the upper skeleton).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_upper_filter`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_upper_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Filtering a decorated output for entries above m returns its stored upper word sigma.

**Theorem 1.7 (Recovering inserted blocks).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_blocks_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_blocks_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Equal decorated outputs with the same n and m have equal lists of lower filler blocks.

**Theorem 1.8 (Recovering the gap vector).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_gap_raw_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_gap_raw_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Equal decorated outputs with the same n and m have equal underlying labelled gap vectors.

**Theorem 1.9 (Recovering the chosen upper subset).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_K_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_K_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Equal decorated outputs with the same n and m have the same selected upper subset K.

**Theorem 1.10 (Injectivity at fixed parameters).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For fixed n, m and k, the decorated output map from TwelveData to lists is injective.

**Theorem 1.11 (The largest fixed point is unique).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_m_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_m_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Under the support bounds, equal decorated outputs must have the same distinguished largest fixed value m, even when their other parameters differ.

**Theorem 1.12 (Avoidance forces the lower word).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.avoiding_lower_filter`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.avoiding_lower_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

An avoiding word on the standard support fixed at m has its entries below m in the unique decreasing order.

**Theorem 1.13 (Normal form of a first-pattern avoider).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.avoiding_twelve_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveInverse.avoiding_twelve_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

An avoiding word fixed at m splits into a lower prefix, m, and upper skeleton entries with lower filler blocks after them; the upper skeleton is its filter above m.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.afterBlocks_injective_blocks`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.avoiding_lower_filter`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.avoiding_twelve_normal_form`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.exists_afterBlocks_decomposition`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.fixedSyntax_decomposition`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.interleaving_blocks_eq`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.takeWhile_filler_prefix`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_K_eq`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_blocks_eq`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_gap_raw_eq`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_injective`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_m_eq`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveInverse.twelveList_upper_filter`
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwelveCount](ArrowWilfTwelveCount.md)
