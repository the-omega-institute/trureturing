# Normalized Stationary Gram

## Abstract

Actual stationary residuals give the full normalized source Gram entries and rank interface.

A and K are finite types, A has decidable equality, blank belongs to A, and Space(K) is complex Euclidean memory. Unitary(A times K) denotes the complex linear isometric automorphisms of the joint alphabet-memory space. Every occurrence of the schedule below is the constant function with value U. The common-final-memory equation ranges over every word and every memory coordinate.

residualMemory, prefixMemory, boxOccupation, and occupationGram are the actual PhysicalGram objects. normalizedResidual, residualScale, and sourceMoment are defined in NormalizedResiduals: the scale is sqrt(M(r)), the normalized vector is its complex inverse times residualMemory, and the moment is inner(Complex,normalizedResidual(r),f). Here M(r) means the existing multiplicity(r.card,r), the number of words of that occupation. The inner product conjugates its first operand; star is complex conjugation. NatToReal, NatToComplex, and ofReal are the indicated canonical scalar embeddings.

**Theorem 1.1 (residual_prefix).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; r \le a \Rightarrow \left(\forall w \in List\left(A\right),\; length\left(w\right) \le card\left(r\right) \Rightarrow prefixMemory\left(blank, U, w, residualMemory\left(a, blank, U, x, r\right)\right) = ite\left(toMultiset\left(w\right) \le r, residualMemory\left(a, blank, U, x, r - toMultiset\left(w\right)\right), 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.residual_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Append every suffix of the remaining length. The existing exact suffix output and injectivity identify the residual when the prefix occupation fits; otherwise every completed word has the wrong occupation and the prefix vector is zero.

**Theorem 1.2 (residual_inner_of_le).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \forall s \in Multiset\left(A\right),\; \left(\left(r \le a \land s \le a\right) \land s \le r\right) \Rightarrow inner\left(Complex, residualMemory\left(a, blank, U, x, r\right), residualMemory\left(a, blank, U, x, s\right)\right) = NatToComplex\left(multiplicity\left(card\left(s\right), s\right)\right) \cdot inner\left(Complex, residualMemory\left(a, blank, U, x, r - s\right), f\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.residual_inner_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the actual inner product over suffixes of length s.card. Exactly multiplicity(s.card,s) suffixes survive on the second residual, and each leaves the first residual at r minus s. This includes s equal to zero and r equal to s.

**Theorem 1.3 (residual_inner_of_not_le).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \forall s \in Multiset\left(A\right),\; \left(\left(\left(r \le a \land s \le a\right) \land card\left(s\right) \le card\left(r\right)\right) \land \neg {s \le r}\right) \Rightarrow inner\left(Complex, residualMemory\left(a, blank, U, x, r\right), residualMemory\left(a, blank, U, x, s\right)\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.residual_inner_of_not_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the shorter occupation does not fit inside the longer one, every potentially surviving suffix on the second residual gives zero on the first.

**Theorem 1.4 (normalized_inner_of_le).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \forall s \in Multiset\left(A\right),\; \left(\left(\left(r \le a \land s \le a\right) \land s \le r\right) \land norm\left(f\right) = 1\right) \Rightarrow inner\left(Complex, normalizedResidual\left(a, blank, U, x, r\right), normalizedResidual\left(a, blank, U, x, s\right)\right) = ofReal\left(\sqrt{\frac{NatToReal\left(multiplicity\left(card\left(s\right), s\right)\right) \cdot NatToReal\left(multiplicity\left(card\left(r - s\right), r - s\right)\right)}{NatToReal\left(multiplicity\left(card\left(r\right), r\right)\right)}}\right) \cdot sourceMoment\left(a, blank, U, x, f, r - s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_inner_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divide the scaled comparable entry by the two positive normalization factors. The remaining source moment keeps the normalized residual in its first operand.

**Theorem 1.5 (normalized_inner_of_ge).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \forall s \in Multiset\left(A\right),\; \left(\left(\left(r \le a \land s \le a\right) \land r \le s\right) \land norm\left(f\right) = 1\right) \Rightarrow inner\left(Complex, normalizedResidual\left(a, blank, U, x, r\right), normalizedResidual\left(a, blank, U, x, s\right)\right) = ofReal\left(\sqrt{\frac{NatToReal\left(multiplicity\left(card\left(r\right), r\right)\right) \cdot NatToReal\left(multiplicity\left(card\left(s - r\right), s - r\right)\right)}{NatToReal\left(multiplicity\left(card\left(s\right), s\right)\right)}}\right) \cdot star\left(sourceMoment\left(a, blank, U, x, f, s - r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_inner_of_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate symmetry gives the reverse comparable entry. The positive real coefficient is unchanged and the source moment is conjugated.

**Theorem 1.6 (normalized_inner_incomparable).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \forall s \in Multiset\left(A\right),\; \left(\left(\left(\left(r \le a \land s \le a\right) \land \neg {s \le r}\right) \land \neg {r \le s}\right) \land norm\left(f\right) = 1\right) \Rightarrow inner\left(Complex, normalizedResidual\left(a, blank, U, x, r\right), normalizedResidual\left(a, blank, U, x, s\right)\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_inner_incomparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compare the two total lengths and apply the shorter incompatible-occupation identity, conjugating if necessary. The occupations need not have equal length.

TailBox(a.count) is the dependent product of Fin(a.count(i)+1) over i in A. boxOccupation(a,r) has counts equal to these coordinate values, so it is legal even when some or all capacities vanish. The following matrices are indexed by this same TailBox on both sides and have complex entries. Matrix.gram uses inner(Complex,v(r),v(s)); Matrix.diagonal has the displayed values on its diagonal and zeros elsewhere.

**Definition 1.7 (normalizedGram).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; normalizedGram\left(a, blank, U, x\right) = gram\left(Complex, r:TailBox\left(i:A \mapsto count\left(a, i\right)\right) \mapsto normalizedResidual\left(a, blank, U, x, boxOccupation\left(a, r\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalizedGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalizedGram is the Gram matrix of the actual normalized residual vectors on the existing box.

**Definition 1.8 (normalizationDiagonal).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; normalizationDiagonal\left(a\right) = diagonal\left(r:TailBox\left(i:A \mapsto count\left(a, i\right)\right) \mapsto ofReal\left(residualScale\left(boxOccupation\left(a, r\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalizationDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalizationDiagonal is the complex matrix with positive real sqrt(M(boxOccupation(a,r))) diagonal entries.

**Theorem 1.9 (diagonal_positive).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in TailBox\left(i:A \mapsto count\left(a, i\right)\right),\; 0 < re\left(normalizationDiagonal\left(a\right)\left(r, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.diagonal_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real diagonal entry is strictly positive, including the zero-occupation coordinate.

**Theorem 1.10 (diagonal_ne_zero).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in TailBox\left(i:A \mapsto count\left(a, i\right)\right),\; normalizationDiagonal\left(a\right)\left(r, r\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.diagonal_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each complex diagonal entry is nonzero.

**Theorem 1.11 (diagonal_det_ne_zero).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; det\left(normalizationDiagonal\left(a\right)\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.diagonal_det_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant is the product of the nonzero diagonal entries.

**Theorem 1.12 (occupation_gram_eq_diagonal).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; occupationGram\left(a, blank, U, x\right) = normalizationDiagonal\left(a\right) \cdot normalizedGram\left(a, blank, U, x\right) \cdot normalizationDiagonal\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.occupation_gram_eq_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scale both actual normalized vectors back to their residual vectors. The left scale is conjugated by the inner product, but equals its conjugate because it is real. This gives exactly B equals D G D.

**Theorem 1.13 (occupation_gram_rank_eq).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; rank\left(occupationGram\left(a, blank, U, x\right)\right) = rank\left(normalizedGram\left(a, blank, U, x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.occupation_gram_rank_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Left and right multiplication by the invertible diagonal preserves the matrix rank.

**Theorem 1.14 (normalized_gram_psd).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; PosSemidef\left(normalizedGram\left(a, blank, U, x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_gram_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex Gram matrix is positive semidefinite.

**Theorem 1.15 (normalized_gram_rank_le).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; rank\left(normalizedGram\left(a, blank, U, x\right)\right) \le FintypeCard\left(K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_gram_rank_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing rank bound for the actual occupationGram transfers through the diagonal rank equality.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.diagonal_det_ne_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.diagonal_ne_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.diagonal_positive`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalizationDiagonal`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalizedGram`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_gram_psd`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_gram_rank_le`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_inner_incomparable`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_inner_of_ge`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.normalized_inner_of_le`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.occupation_gram_eq_diagonal`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.occupation_gram_rank_eq`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.residual_inner_of_le`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.residual_inner_of_not_le`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedGram.residual_prefix`
- Dependency: [D5/S3/Quantum/StationaryPreparation/NormalizedResiduals](NormalizedResiduals.md)
