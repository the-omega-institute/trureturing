# Inverting the Second Decorated Construction

## Abstract

The second decorated description is a bijection with the nonexceptional smallest-fixed-point fiber.

**Definition 1.1 (The smallest-fixed-point fiber).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.MinAvoiders`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.MinAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The subtype consists of avoiding words on the standard support fixed at m and with no fixed value below m.

**Definition 1.2 (Decorated data land in the fiber).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.minAvoiderOfData`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.minAvoiderOfData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When one at most m less than n, a TwentyThreeData object yields an avoider whose smallest hat-fixed value is m.

**Theorem 1.3 (Normal form of a smallest-fixed avoider).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.minAvoider_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.minAvoider_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Every such avoider splits into a lower prefix, m, and the decreasing upper skeleton with lower filler blocks after each upper entry.

**Theorem 1.4 (The lower prefix has no fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.normal_prefix_no_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.normal_prefix_no_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The lower prefix of the normal form has no hat-fixed value among its entries.

**Theorem 1.5 (Partition of lower support).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.normal_support_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.normal_support_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The flattened fillers form a subset of the lower support, the prefix set is its complement there, and both lower lists have distinct entries.

**Theorem 1.6 (The recovered lower words).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.normal_lower_words`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.normal_lower_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The normal prefix is a word with no fixed point on its support, and the flattened filler blocks form a word on the complementary lower support.

**Theorem 1.7 (Recover the upper gap vector).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.upper_gaps_of_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.upper_gaps_of_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A block list aligned with the decreasing upper skeleton determines an upper-labelled gap vector whose readout is the list of block lengths.

**Theorem 1.8 (Every smallest-fixed avoider is decorated).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.minAvoider_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.minAvoider_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Every avoiding word in the nonexceptional fiber equals the output of some TwentyThreeData(n,m,r).

**Theorem 1.9 (A leading filler block is unique).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.filler_prefix_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.filler_prefix_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When two separated words meet at the same first skeleton entry, equality determines both leading filler blocks and remaining tails.

**Theorem 1.10 (The upper filler blocks are unique).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.afterBlocks_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.afterBlocks_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For a fixed skeleton separated by a predicate from its fillers, equality of interleaved outputs forces equality of aligned filler-block lists.

**Theorem 1.11 (Gap lengths determine their vector).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.upperGapSizes_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.upperGapSizes_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Two gap vectors on the same upper support and with the same ordered upper gap lengths are equal.

**Theorem 1.12 (A split at a unique value is unique).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.split_at_member_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.split_at_member_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If m is absent from both prefixes, equal words split at m have equal prefixes and suffixes.

**Theorem 1.13 (Bounds for decorated normal forms).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.data_normal_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.data_normal_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The decorated prefix lies below m, the filler-block count matches the upper skeleton, every filler lies below m, and the flattened blocks recover rho.

**Theorem 1.14 (Uniqueness of decorated data).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.twentyThreeList_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.twentyThreeList_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Equal outputs with the same n and m have equal r and heterogeneously equal decorated data.

**Definition 1.15 (The full decorated fiber).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.TwentyThreeFamily`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.TwentyThreeFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The family is the dependent sum of TwentyThreeData(n,m,r) over r less than m.

**Definition 1.16 (Map the family to the fiber).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.twentyThreeFamilyMap`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.twentyThreeFamilyMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Each object in the dependent decorated family maps to its avoiding word with smallest fixed point m.

**Definition 1.17 (The nonexceptional bijection).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.twentyThreeFamilyEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.twentyThreeFamilyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For positive m below n, the complete decorated family is equivalent to the avoidance fiber with smallest fixed point m.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.MinAvoiders`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.TwentyThreeFamily`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.afterBlocks_unique`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.data_normal_bounds`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.filler_prefix_unique`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.minAvoiderOfData`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.minAvoider_normal_form`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.minAvoider_surjective`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.normal_lower_words`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.normal_prefix_no_fixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.normal_support_split`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.split_at_member_unique`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.twentyThreeFamilyEquiv`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.twentyThreeFamilyMap`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.twentyThreeList_unique`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.upperGapSizes_injective`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.upper_gaps_of_blocks`
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwelveSurject](ArrowWilfTwelveSurject.md)
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwentyThreeCount](ArrowWilfTwentyThreeCount.md)
