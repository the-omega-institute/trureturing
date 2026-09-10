# Exact Padding Gram Ranks

## Abstract

Exact individual and aggregate ranks of the actual padding Gram.

A is finite with decidable equality, h is a letter, and a is any occupation multiset. R(a) is the dependent product of Fin(count(i,a)+1); boxCard(a) is the product over all letters i of count(i,a)+1. T(a,h) restricts that product to the tail letters unequal to h, and zeroTail(a,h) is its all-zero element. All ranks below are complex matrix ranks. paddingGram, normalizedPaddingGram, paddingBlock, and the exact occupationSplit are the actual vector matrices defined in PaddingBlocks.

**Theorem 1.1 (padding_block_rank_zero).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; rank\left(paddingBlock\left(h, a, zeroTail\left(a, h\right)\right)\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.padding_block_rank_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prescribed diagonal has one nonzero entry at head index zero. The two lower-ones factors are invertible, so the zero-tail block has rank one.

**Theorem 1.2 (padding_block_rank_positive).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; b \ne zeroTail\left(a, h\right) \Rightarrow rank\left(paddingBlock\left(h, a, b\right)\right) = count\left(h, a\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.padding_block_rank_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero tail all real difference pivots are strictly positive. The block therefore has full rank count(h,a)+1, also when count(h,a)=0.

**Theorem 1.3 (padding_gram_rank).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; rank\left(paddingGram\left(h, a\right)\right) = boxCard\left(a\right) - count\left(h, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.padding_gram_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindex the actual complete occupation Gram by (head,tail), and combine the prescribed factors with blockDiagonal. Diagonal rank counts its nonzero entries. The zero entries correspond exactly to (j,zeroTail) with j nonzero; this set has count(h,a) elements. Subtracting from the actual occupation carrier gives the displayed aggregate rank. This conclusion is a matrix-rank equality.

**Theorem 1.4 (normalized_padding_gram_rank).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; rank\left(normalizedPaddingGram\left(h, a\right)\right) = boxCard\left(a\right) - count\left(h, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.normalized_padding_gram_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive normalization diagonal preserves rank on both sides.

**Theorem 1.5 (maximal_padding_gram_rank).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; count\left(h, a\right) = maximumCapacity\left(a\right) \Rightarrow rank\left(normalizedPaddingGram\left(h, a\right)\right) = boxCard\left(a\right) - maximumCapacity\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.maximal_padding_gram_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

maximumCapacity(a) denotes Finset.univ.sup(a.count). This source specialization has the explicit maximality premise. The general block and aggregate theorems hold for any chosen head.

**Theorem 1.6 (zero_padding_gram_rank).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; rank\left(normalizedPaddingGram\left(h, 0\right)\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.zero_padding_gram_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the all-zero occupation, the actual normalized Gram has rank one.

**Theorem 1.7 (occupation_5040_padding_gram_rank).**

$$rank\left(paddingGram\left(none, occupation5040\right)\right) = 1 + 11 \cdot 5 \land rank\left(normalizedPaddingGram\left(none, occupation5040\right)\right) = 56$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.occupation_5040_padding_gram_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

occupation5040 is the existing CoherentHistorySchmidt.occupation5040, defined as capacityOccupation(4, tailCapacities5040), on Option(Fin(3)); its head is none and its tail capacities are exactly (2,1,1). There are twelve tail occupations, eleven nonzero; the zero-tail rank is one and each positive-tail block has rank five. The actual aggregate ranks are therefore 1+11*5=56.

**Theorem 1.8 (physical_source_moments).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; r \le a \Rightarrow sourceMoment\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), physicalFinal\left(a\right), r\right) = if\left(tailCount\left(maximalHead\left(a\right), r\right) = 0, 1, 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_source_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With nonempty A, PaddingBlocks identifies B's actual prefix-derived normalized memories with C's embedded padding vectors for the chosen physicalGate and initial vector. Thus B's source moments are one exactly on the legal head axis and zero elsewhere. The inner product has the normalized residual first and common physicalFinal second.

**Theorem 1.9 (physical_source_gram_rank).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; rank\left(normalizedGram\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right)\right)\right) = boxCard\left(a\right) - maximumCapacity\left(a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_source_gram_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identified B normalized Gram of the actual C circuit has product-minus-maximum rank. The identification and the rank are proved; neither is an assumption.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.maximal_padding_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.normalized_padding_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.occupation_5040_padding_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.padding_block_rank_positive`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.padding_block_rank_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.padding_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_source_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_source_moments`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.zero_padding_gram_rank`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingBlocks](PaddingBlocks.md)
