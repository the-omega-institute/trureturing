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

For the following statements A is also nonempty. Write h=maximalHead(a) and d=proposedDimension(a). Space(I) is the complex Euclidean space indexed by I. The displayed normalizedResidual is the actual prefix-derived residual for physicalGate(a) and paddingInitial(a), divided by ofReal(residualScale(r)); residualScale(r) is sqrt(NatToReal(multiplicity(card(r),r))). The initial padding vector is scaled once by the inverse of residualScale(a).

TensorProduct(Complex,E,F) is the tensor product over the complex numbers, and tmul(Complex,x,y) puts the letter vector x first and the memory vector y second. LinearIsometry(Complex,E,F) denotes the complex linear isometries from E to F. For the tensor product of the two displayed orthonormal bases, repr maps a tensor to coordinates indexed by (letter,memory). Its inverse, regarded as a linear isometry, is composed with the existing emission. Thus the local V below is fixed by a and is independent of r and time. NatToReal casts a natural number to the reals; ofReal then embeds the real square root into the complex numbers. smul is complex scalar multiplication.

**Theorem 1.10 (physical_normalized_emission).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; \left(r \le a \land r \ne 0\right) \Rightarrow let V:LinearIsometry\left(Complex, Space\left(Fin\left(proposedDimension\left(a\right)\right)\right), TensorProduct\left(Complex, Space\left(A\right), Space\left(Fin\left(proposedDimension\left(a\right)\right)\right)\right)\right) = comp\left(toLinearIsometry\left(symm\left(repr\left(tensorProduct\left(basisFun\left(A, Complex\right), basisFun\left(Fin\left(proposedDimension\left(a\right)\right), Complex\right)\right)\right)\right)\right), emission\left(maximalHead\left(a\right), physicalGate\left(a\right)\right)\right) in V\left(normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), r\right)\right) = \sum_{i:A}{smul\left(ofReal\left(\sqrt{\frac{NatToReal\left(count\left(i, r\right)\right)}{NatToReal\left(card\left(r\right)\right)}}\right), tmul\left(Complex, basis\left(i\right), normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), erase\left(r, i\right)\right)\right)\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_emission` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a legal nonzero remaining occupation, the actual fixed circuit has the prescribed square-root emission amplitudes. Its all-word output gives the normalized letter equations. Applying the tensor basis representation assembles those coordinates into the displayed equality. Absent letters have count zero, so their summands vanish even though erase is defined for them.

**Theorem 1.11 (physical_normalized_terminal_emission).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; let V:LinearIsometry\left(Complex, Space\left(Fin\left(proposedDimension\left(a\right)\right)\right), TensorProduct\left(Complex, Space\left(A\right), Space\left(Fin\left(proposedDimension\left(a\right)\right)\right)\right)\right) = comp\left(toLinearIsometry\left(symm\left(repr\left(tensorProduct\left(basisFun\left(A, Complex\right), basisFun\left(Fin\left(proposedDimension\left(a\right)\right), Complex\right)\right)\right)\right)\right), emission\left(maximalHead\left(a\right), physicalGate\left(a\right)\right)\right) in V\left(normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), 0\right)\right) = tmul\left(Complex, basis\left(maximalHead\left(a\right)\right), normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_terminal_emission` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized zero residual is the embedded padding basis vector at none. The actual gate fixes the joint basis vector (h,none), so this terminal memory emits h and remains unchanged. This equality includes a=0 and requires no positive head count.

**Theorem 1.12 (physical_normalized_dependencies).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall J \in Type,\; Fintype\left(J\right) \Rightarrow \left(\forall r \in J \to Multiset\left(A\right),\; \forall c \in J \to Complex,\; \left(\forall j \in J,\; r\left(j\right) \le a\right) \Rightarrow \left(\sum_{j:J}{smul\left(c\left(j\right), normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), r\left(j\right)\right)\right)} = 0 \Rightarrow \sum_{j:J}{smul\left(c\left(j\right), if\left(r\left(j\right) = 0, tmul\left(Complex, basis\left(maximalHead\left(a\right)\right), normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), 0\right)\right), \sum_{i:A}{smul\left(ofReal\left(\sqrt{\frac{NatToReal\left(count\left(i, r\left(j\right)\right)\right)}{NatToReal\left(card\left(r\left(j\right)\right)\right)}}\right), tmul\left(Complex, basis\left(i\right), normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), erase\left(r\left(j\right), i\right)\right)\right)\right)}\right)\right)} = 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_dependencies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be any finite type, r any family of legal residual occupations, and c any complex coefficients. Repetitions and zero residuals are allowed. Apply the same complex linear isometry V to the assumed zero sum. For each index, the terminal emission equality supplies the zero branch and the nonzero emission equality supplies the other branch of if. Both are required for the resulting prescribed tensor sum to vanish.

**Theorem 1.13 (physical_normalized_span).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; span\left(Complex, \{v:Space\left(Fin\left(proposedDimension\left(a\right)\right)\right) \mid \exists r \in Multiset\left(A\right),\; r \le a \land v = normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), r\right)\}\right) = top\left(Submodule\left(Complex, Space\left(Fin\left(proposedDimension\left(a\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex span of all actual legal normalized residuals is the whole physical memory space. Restrict the boxOccupation-indexed family to this subspace. Its inner products give exactly the actual normalizedGram. physical_source_gram_rank identifies its rank with d. Factoring that Gram through orthonormal coordinates in the subspace bounds d by its finrank; the ambient space has finrank d, hence the subspace is top.

**Theorem 1.14 (physical_normalized_zero_eq_head).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; 0 < count\left(maximalHead\left(a\right), a\right) \Rightarrow normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), 0\right) = normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), replicate\left(1, maximalHead\left(a\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_zero_eq_head` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the chosen head has positive count, its singleton is legal. Both its normalized padding vector and the zero normalized padding vector are exactly basis(none). Their identical coordinate embeddings give equality of the actual residuals, including their complex phase.

**Theorem 1.15 (physical_normalized_nonterminal_span).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(Nonempty\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; 0 < count\left(maximalHead\left(a\right), a\right) \Rightarrow span\left(Complex, \{v:Space\left(Fin\left(proposedDimension\left(a\right)\right)\right) \mid \exists r \in Multiset\left(A\right),\; r \le a \land \left(r \ne 0 \land v = normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), paddingInitial\left(a\right), r\right)\right)\}\right) = top\left(Submodule\left(Complex, Space\left(Fin\left(proposedDimension\left(a\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_nonterminal_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the positive head-count condition, remove the zero occupation from the generating family. Every nonzero generator remains, and the zero generator equals the legal nonzero head singleton by the preceding equality. The full span result therefore gives the same whole memory space. For a=0 the memory dimension is one and the nonterminal family is empty; the positive head-count condition excludes that case.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.maximal_padding_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.normalized_padding_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.occupation_5040_padding_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.padding_block_rank_positive`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.padding_block_rank_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.padding_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_dependencies`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_emission`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_nonterminal_span`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_span`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_terminal_emission`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_normalized_zero_eq_head`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_source_gram_rank`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.physical_source_moments`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingRanks.zero_padding_gram_rank`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingBlocks](PaddingBlocks.md)
