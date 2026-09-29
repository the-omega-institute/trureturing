# Gap Vectors and Interleaved Words

## Abstract

Weak compositions record where lower entries are inserted around a permutation skeleton.

**Definition 1.1 (Labelled weak compositions).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.GapsOn`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.GapsOn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

GapsOn(iota,t) is the finite type of nonnegative vectors indexed by iota whose entries sum to t.

**Definition 1.2 (Linear weak compositions).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.Gaps`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.Gaps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Gaps(r,t) specializes labelled gap vectors to the index set Fin(r).

**Definition 1.3 (List of gap lengths).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.gapList`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.gapList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Reading a vector in the standard order of Fin(r) gives its list of r nonnegative parts.

**Definition 1.4 (Positive prescribed gaps).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.PositiveGapsOn`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.PositiveGapsOn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

This subtype requires each gap indexed by R to have positive length while the total length remains t.

**Definition 1.5 (Positive linear gaps).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.PositiveGaps`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.PositiveGaps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

PositiveGaps(r,t,R) is the linear-index specialization of PositiveGapsOn.

**Definition 1.6 (Mandatory units).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.gapIndicator`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.gapIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The indicator vector has value one on R and zero at every other gap label.

**Definition 1.7 (Removing mandatory units).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.positiveGapsEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.positiveGapsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When the cardinality of R is at most t, subtracting one in every prescribed slot identifies positive gaps of total t with ordinary gaps of total t minus the cardinality of R.

**Definition 1.8 (A gap following a value).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.gapAt`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.gapAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The gap following a support value x is read from the label some x, and is zero outside the support.

**Definition 1.9 (Gap lengths in skeleton order).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.gapSizes`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.gapSizes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The gap list begins with the leading gap and then reads the remaining labels in the order of a word on the upper support.

**Theorem 1.10 (Length and total of gap sizes).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.gapSizes_length_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfGapData.gapSizes_length_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The list of gaps has one more entry than the support has values, and the sum of its entries is t.

**Definition 1.11 (Interleaving after skeleton entries).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.afterBlocks`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfGapData.afterBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The first filler block follows the first skeleton value, the second follows the second, and so on; extra blocks are ignored once the skeleton ends.

**Theorem 1.12 (Interleaving preserves the values).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.afterBlocks_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfGapData.afterBlocks_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

With equal numbers of blocks and skeleton entries, the interleaved word permutes the skeleton followed by all flattened blocks.

**Theorem 1.13 (Recovering the skeleton).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.filter_afterBlocks_skeleton`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfGapData.filter_afterBlocks_skeleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If the predicate holds on all skeleton entries and no filler entry, filtering the interleaving by the predicate returns the skeleton.

**Theorem 1.14 (Recovering the fillers).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.filter_afterBlocks_fillers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfGapData.filter_afterBlocks_fillers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Under the same separation of skeleton and filler entries, filtering by the complement of the predicate returns the flattened filler blocks.

**Theorem 1.15 (A lower prefix preserves singleton syntax).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.fixedSyntax_append_small_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfGapData.fixedSyntax_append_small_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A prefix whose values all lie below g does not change FixedSyntax g for a suffix that contains g.

**Theorem 1.16 (A low filler destroys a singleton block).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfGapData.fixedSyntax_afterBlocks_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfGapData.fixedSyntax_afterBlocks_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For a skeleton with distinct entries and filler entries below g, g has singleton syntax after interleaving exactly when it had singleton syntax in the skeleton and its following filler block is empty.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.Gaps`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.GapsOn`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.PositiveGaps`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.PositiveGapsOn`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.afterBlocks`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.afterBlocks_perm`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.filter_afterBlocks_fillers`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.filter_afterBlocks_skeleton`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.fixedSyntax_afterBlocks_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.fixedSyntax_append_small_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.gapAt`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.gapIndicator`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.gapList`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.gapSizes`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.gapSizes_length_sum`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfGapData.positiveGapsEquiv`
- Dependency: [D5/S3/Combinatorics/ArrowWilfCountingCore](ArrowWilfCountingCore.md)
