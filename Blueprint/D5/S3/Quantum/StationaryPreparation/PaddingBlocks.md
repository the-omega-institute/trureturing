# The Prescribed Padding Gram Factorization

## Abstract

Actual padding occupation blocks and their prescribed difference factorization.

A is a finite type with decidable equality, h is a letter, and a is an arbitrary occupation multiset. Its capacities are count(i,a), hence nonnegative. R(a)=TailBox(a.count) is the dependent product of Fin(count(i,a)+1). T(a,h) is the same dependent product restricted to letters i unequal to h. The selected h need not be maximal for the block identities. All matrix scalars are complex; blockMass and blockDifference are real. Nat subtraction j-1 is truncated at zero. val denotes the natural value of a Fin index.

**Definition 1.1 (occupationSplit).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; occupationSplit\left(h, a\right) = piSplitAt\left(h, i:A \mapsto Fin\left(count\left(i, a\right) + 1\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.occupationSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing dependent-function equivalence sends r to (r(h), its tail). Its inverse restores exactly these bounded coordinates.

**Definition 1.2 (blockOccupation).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; \forall j \in \mathbb{N},\; blockOccupation\left(h, a, b, j\right) = headSlice\left(h, boxOccupation\left(a, inverseApply\left(occupationSplit\left(h, a\right), pair\left(0, b\right)\right)\right), j\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.blockOccupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero-head box representative fixes the actual tail. headSlice replaces only its head count. Scalar masses may use any natural j; actual block vectors use j in Fin(count(h,a)+1). inverseApply(e,x) means e.symm(x).

**Theorem 1.3 (block_occupation_index).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; \forall j \in Fin\left(count\left(h, a\right) + 1\right),\; blockOccupation\left(h, a, b, val\left(j\right)\right) = boxOccupation\left(a, inverseApply\left(occupationSplit\left(h, a\right), pair\left(j, b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_occupation_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The head slice is exactly the occupation of the inverse box index. Thus every matrix vector below is an actual legal paddingResidual.

**Theorem 1.4 (block_occupation_tail).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; \forall j \in \mathbb{N},\; tailCount\left(h, blockOccupation\left(h, a, b, j\right)\right) = tailSum\left(b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_occupation_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tail cardinality is the sum of the actual bounded tail coordinates.

**Definition 1.5 (blockMass).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; \forall j \in \mathbb{N},\; blockMass\left(h, a, b, j\right) = NatToReal\left(multiplicity\left(card\left(blockOccupation\left(h, a, b, j\right)\right), blockOccupation\left(h, a, b, j\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.blockMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is m_j=M(j,b), the exact occupation-word multiplicity, included in the reals.

**Definition 1.6 (blockDifference).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; \forall j \in \mathbb{N},\; blockDifference\left(h, a, b, j\right) = if\left(j = 0, blockMass\left(h, a, b, 0\right), blockMass\left(h, a, b, j\right) - blockMass\left(h, a, b, j - 1\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.blockDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

if(P,x,y) is the ternary conditional. The diagonal starts with m_0, then the consecutive differences m_j-m_(j-1).

**Definition 1.7 (lowerOnes).**

$$\forall H \in \mathbb{N},\; \forall j \in Fin\left(H + 1\right),\; \forall k \in Fin\left(H + 1\right),\; lowerOnes\left(H\right)\left(j, k\right) = if\left(k \le j, 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.lowerOnes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prescribed matrix has literal ones on and below the diagonal and zero above it.

**Definition 1.8 (paddingBlock).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; paddingBlock\left(h, a, b\right) = gram\left(Complex, j:Fin\left(count\left(h, a\right) + 1\right) \mapsto paddingResidual\left(h, a, blockOccupation\left(h, a, b, val\left(j\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.paddingBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The block is the complex Gram of actual C padding vectors with this tail.

**Definition 1.9 (paddingGram).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; paddingGram\left(h, a\right) = gram\left(Complex, r:R\left(a\right) \mapsto paddingResidual\left(h, a, boxOccupation\left(a, r\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.paddingGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The aggregate scaled Gram uses the existing complete occupation index R(a).

**Definition 1.10 (normalizedPaddingGram).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; normalizedPaddingGram\left(h, a\right) = gram\left(Complex, r:R\left(a\right) \mapsto normalizedPadding\left(h, a, boxOccupation\left(a, r\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.normalizedPaddingGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized Gram uses the same actual vectors divided by their positive word-count scales.

**Theorem 1.11 (padding_gram_eq_diagonal).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; paddingGram\left(h, a\right) = normalizationDiagonal\left(a\right) \cdot normalizedPaddingGram\left(h, a\right) \cdot normalizationDiagonal\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_gram_eq_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing normalizationDiagonal has entries sqrt(M(r)), included in the complex numbers. The inner product conjugates its first operand; these real diagonal entries are unchanged. This is exactly B=DGD on the actual vectors.

**Theorem 1.12 (padding_gram_rank_eq).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; rank\left(paddingGram\left(h, a\right)\right) = rank\left(normalizedPaddingGram\left(h, a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_gram_rank_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive diagonal is invertible, so both Gram ranks agree.

**Theorem 1.13 (padding_block_entry).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; \forall j \in Fin\left(count\left(h, a\right) + 1\right),\; \forall k \in Fin\left(count\left(h, a\right) + 1\right),\; paddingBlock\left(h, a, b\right)\left(j, k\right) = ofReal\left(blockMass\left(h, a, b, min\left(val\left(j\right), val\left(k\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_block_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entries in a fixed tail block are exactly m_min(j,k).

**Theorem 1.14 (padding_gram_blocks).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; reindex\left(paddingGram\left(h, a\right), occupationSplit\left(h, a\right), occupationSplit\left(h, a\right)\right) = blockDiagonal\left(b:T\left(a, h\right) \mapsto paddingBlock\left(h, a, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_gram_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

blockDiagonal has index (head,tail). Its entry is this tail's block when the two entire tails are equal, and zero otherwise. This identifies the actual aggregate matrix, including distinct tails of equal cardinality.

**Theorem 1.15 (lower_ones_det).**

$$\forall H \in \mathbb{N},\; det\left(lowerOnes\left(H\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.lower_ones_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower triangular diagonal consists of ones.

**Theorem 1.16 (padding_block_factorization).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; paddingBlock\left(h, a, b\right) = lowerOnes\left(count\left(h, a\right)\right) \cdot diagonal\left(j:Fin\left(count\left(h, a\right) + 1\right) \mapsto ofReal\left(blockDifference\left(h, a, b, val\left(j\right)\right)\right)\right) \cdot transpose\left(lowerOnes\left(count\left(h, a\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_block_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the literal matrix product sums consecutive differences up to min(j,k). The finite telescoping identity gives exactly m_min(j,k). The transpose is ordinary transpose, as in the source; the factor's entries are real ones and zeros.

**Theorem 1.17 (block_difference_pos).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; b \ne zeroTail\left(a, h\right) \Rightarrow \left(\forall j \in \mathbb{N},\; 0 < blockDifference\left(h, a, b, j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_difference_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive tail, each difference is the existing strictly positive last-tail mass of the actual head slice. This includes the initial difference at j=0.

**Theorem 1.18 (block_mass_strict).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in T\left(a, h\right),\; b \ne zeroTail\left(a, h\right) \Rightarrow \left(\forall j \in \mathbb{N},\; 0 < j \Rightarrow blockMass\left(h, a, b, j - 1\right) < blockMass\left(h, a, b, j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_mass_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j>0 the positive difference proves the strict growth required by the source's ratio argument. No division by a zero head index is used.

**Theorem 1.19 (block_difference_zero_tail).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall j \in \mathbb{N},\; blockDifference\left(h, a, zeroTail\left(a, h\right), j\right) = if\left(j = 0, 1, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_difference_zero_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For zero tail every head occupation has multiplicity one; exactly the initial pivot survives.

For the following identifications A is also nonempty. The existing maximalHead(a), physicalGate(a), physicalMemoryEquiv(a), physicalResidual(a,r), and physicalFinal(a) are C's actual chosen construction. proposedDimension(a) is the product of capacities plus one, minus the maximum capacity. E(a) is coordinateEmbedding(physicalMemoryEquiv(a).toEmbedding). The B names residualMemory, normalizedResidual, sourceMoment and normalizedGram retain their existing prefix-derived meanings; the following equalities identify the two families.

**Definition 1.20 (paddingInitial).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; paddingInitial\left(a\right) = smulC\left(inv\left(ofReal\left(residualScale\left(a\right)\right)\right), physicalResidual\left(a, a\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.paddingInitial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is exactly C's chosen normalized initial vector, in Space(Fin(proposedDimension(a))).

**Theorem 1.21 (padding_residual_identification).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; r \le a \Rightarrow residualMemory\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), r\right) = physicalResidual\left(a, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_residual_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C's proved local residual steps give the output of every suffix. B's residual output has the same coefficients and terminal memory. Suffix injectivity identifies the actual vectors, with no identity or rank assumption.

**Theorem 1.22 (normalized_padding_identification).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; r \le a \Rightarrow normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), r\right) = E\left(a\right)\left(normalizedPadding\left(maximalHead\left(a\right), a, r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.normalized_padding_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive normalization scale is the same and the coordinate embedding is complex linear.

**Theorem 1.23 (padding_source_moment_identification).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; r \le a \Rightarrow sourceMoment\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), physicalFinal\left(a\right), r\right) = paddingMoment\left(maximalHead\left(a\right), a, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_source_moment_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

E(a) sends the padding sink to physicalFinal(a) and preserves the ordered inner product.

**Theorem 1.24 (padding_normalized_gram_identification).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; normalizedGram\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right)\right) = normalizedPaddingGram\left(maximalHead\left(a\right), a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_normalized_gram_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual prefix-derived B Gram equals the actual normalized padding Gram entry by entry.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.blockDifference`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.blockMass`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.blockOccupation`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_difference_pos`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_difference_zero_tail`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_mass_strict`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_occupation_index`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.block_occupation_tail`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.lowerOnes`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.lower_ones_det`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.normalizedPaddingGram`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.normalized_padding_identification`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.occupationSplit`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.paddingBlock`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.paddingGram`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.paddingInitial`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_block_entry`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_block_factorization`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_gram_blocks`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_gram_eq_diagonal`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_gram_rank_eq`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_normalized_gram_identification`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_residual_identification`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingBlocks.padding_source_moment_identification`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingGram](PaddingGram.md)
