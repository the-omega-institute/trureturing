# Recovering First-Pattern Decorated Data

## Abstract

Every first-pattern avoider with a largest fixed point has the prescribed decorated form.

**Definition 1.1 (Lengths of inserted blocks).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.blockLengths`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveSurject.blockLengths` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The label none stores the initial filler length, while each support-value label stores the length of the block aligned with that value in the skeleton word.

**Theorem 1.2 (Alignment of block lengths).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.blockLengths_aligned`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveSurject.blockLengths_aligned` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Reading the labelled lengths in skeleton order gives exactly the list of lengths of the aligned blocks.

**Definition 1.3 (Gap vector recovered from blocks).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.gapsOfBlocks`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveSurject.gapsOfBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The initial block and the blocks following support values determine a labelled gap vector with the same total filler length.

**Definition 1.4 (The upper subsequence).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.upperWord`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwelveSurject.upperWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Filtering a word on the full support for entries above m gives a word on the upper support.

**Theorem 1.5 (Recovering blocks from their lengths).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.splitLengths_map_length_flatten`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveSurject.splitLengths_map_length_flatten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Splitting the flattening of any list of blocks by that list of block lengths reconstructs the original block list.

**Theorem 1.6 (Upper fixed points require fillers).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.positive_block_of_no_upper_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveSurject.positive_block_of_no_upper_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If an upper skeleton value is fixed there but not in the full word, its following filler block has positive length.

**Theorem 1.7 (Positive slots fit the total).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.positiveGaps_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveSurject.positiveGaps_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The number of slots required to be positive cannot exceed the total sum of all gap lengths.

**Theorem 1.8 (Every largest-fixed avoider is decorated).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.exists_twelveData_of_largest_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveSurject.exists_twelveData_of_largest_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

An avoiding word on the standard support whose largest hat-fixed value is m equals the decorated output of some TwelveData(n,m,k) with k at most n minus m.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.blockLengths`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.blockLengths_aligned`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.exists_twelveData_of_largest_fixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.gapsOfBlocks`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.positiveGaps_card_le`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.positive_block_of_no_upper_fixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.splitLengths_map_length_flatten`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveSurject.upperWord`
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwelveInverse](ArrowWilfTwelveInverse.md)
