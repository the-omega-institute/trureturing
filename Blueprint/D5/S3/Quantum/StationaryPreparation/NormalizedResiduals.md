# Normalized Stationary Residuals

## Abstract

Actual normalized residual memories obey the stationary source amplitudes.

A and K are finite types, A has decidable equality, and blank is a symbol of A. Space(K) is the complex Euclidean space on K. Unitary(A times K) is its complex linear isometric automorphism type on the joint alphabet-memory space. The same U acts at every circuit step. The output hypothesis below quantifies every word and memory coordinate, with one common final vector f.

multiplicity(n,r), occupation, and sectorVector are the objects of OccupancyWordSectors. multiplicity counts length-n words of occupation r. sectorVector(n,r) is its inverse-square-root coefficient on these words and zero otherwise. residualMemory, prefixMemory, and letter are the actual PhysicalGram objects: the residual uses a representative prefix of occupation a minus r applied to sqrt(multiplicity(a.card,a)) times x. ListOfFn enumerates a finite word in order. NatToReal and NatToComplex are the canonical natural casts; ofReal embeds a real number into the complex numbers. smul denotes complex scalar multiplication. The inner product is conjugate-linear in its first operand.

**Definition 1.1 (residualScale).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; residualScale\left(r\right) = \sqrt{NatToReal\left(multiplicity\left(card\left(r\right), r\right)\right)}\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.residualScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

residualScale(r) is a real number: the positive square root of the word multiplicity.

**Definition 1.2 (normalizedResidual).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall r \in Multiset\left(A\right),\; normalizedResidual\left(a, blank, U, x, r\right) = smul\left(inv\left(ofReal\left(residualScale\left(r\right)\right)\right), residualMemory\left(a, blank, U, x, r\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalizedResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalizedResidual(a,blank,U,x,r) lies in Space(K) and is the actual residual divided by its real scale.

**Definition 1.3 (sourceMoment).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \forall r \in Multiset\left(A\right),\; sourceMoment\left(a, blank, U, x, f, r\right) = inner\left(Complex, normalizedResidual\left(a, blank, U, x, r\right), f\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.sourceMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceMoment(a,blank,U,x,f,r) is complex. Its first inner-product operand is the normalized residual.

**Theorem 1.4 (multiplicity_ne_zero).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; multiplicity\left(card\left(r\right), r\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.multiplicity_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing positive word count makes every normalization denominator nonzero, including r equal to zero.

**Theorem 1.5 (scale_pos).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; 0 < residualScale\left(r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive multiplicity has a strictly positive real square root.

**Theorem 1.6 (scale_ne_zero).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; ofReal\left(residualScale\left(r\right)\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive real scale remains nonzero after embedding into the complex numbers.

**Theorem 1.7 (scale_sq).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; residualScale\left(r\right)^{2} = NatToReal\left(multiplicity\left(card\left(r\right), r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squaring the scale recovers the word count.

**Theorem 1.8 (scale_zero).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow residualScale\left(0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty word is the single word of zero occupation, so its scale is one.

**Theorem 1.9 (scale_normalized).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall r \in Multiset\left(A\right),\; smul\left(ofReal\left(residualScale\left(r\right)\right), normalizedResidual\left(a, blank, U, x, r\right)\right) = residualMemory\left(a, blank, U, x, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the normalized vector by its scale recovers the same actual residual.

**Theorem 1.10 (prefix_inner_sum).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall n \in \mathbb{N},\; \forall x \in Space\left(K\right),\; \forall y \in Space\left(K\right),\; inner\left(Complex, x, y\right) = \sum_{w:Fin\left(n\right) \to A}{inner\left(Complex, prefixMemory\left(blank, U, ListOfFn\left(w\right), x\right), prefixMemory\left(blank, U, ListOfFn\left(w\right), y\right)\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.prefix_inner_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Initialize an n-letter blank register and apply the fixed-unitary circuit. Both maps are isometries. Expanding their inner product in all word and memory coordinates gives this sum of actual prefix-memory inner products.

**Theorem 1.11 (residual_inner_self).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \left(r \le a \land norm\left(f\right) = 1\right) \Rightarrow inner\left(Complex, residualMemory\left(a, blank, U, x, r\right), residualMemory\left(a, blank, U, x, r\right)\right) = NatToComplex\left(multiplicity\left(card\left(r\right), r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.residual_inner_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each complete suffix of occupation r produces f; every other suffix of that length produces zero. The all-word inner-product sum therefore counts exactly multiplicity(r.card,r).

**Theorem 1.12 (residual_norm_sq).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \left(r \le a \land norm\left(f\right) = 1\right) \Rightarrow norm\left(residualMemory\left(a, blank, U, x, r\right)\right)^{2} = NatToReal\left(multiplicity\left(card\left(r\right), r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.residual_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the real part of the residual inner-self identity gives its squared norm.

**Theorem 1.13 (normalized_norm).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \left(r \le a \land norm\left(f\right) = 1\right) \Rightarrow norm\left(normalizedResidual\left(a, blank, U, x, r\right)\right) = 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual norm equals its positive real scale; division yields a unit vector for every legal r.

**Theorem 1.14 (normalized_zero).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow normalizedResidual\left(a, blank, U, x, 0\right) = f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized terminal residual is exactly the common final memory, including phase.

**Theorem 1.15 (normalized_initial).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; normalizedResidual\left(a, blank, U, x, a\right) = x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At remaining occupation a the representative prefix is empty; normalization recovers x.

**Theorem 1.16 (source_moment_zero).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(norm\left(f\right) = 1 \Rightarrow sourceMoment\left(a, blank, U, x, f, 0\right) = 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.source_moment_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final memory has unit norm, so its inner product with itself is one.

**Theorem 1.17 (prefix_normalized).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; r \le a \Rightarrow \left(\forall u \in List\left(A\right),\; toMultiset\left(u\right) = a - r \Rightarrow prefixMemory\left(blank, U, u, x\right) = smul\left(ofReal\left(\sqrt{\frac{NatToReal\left(multiplicity\left(card\left(r\right), r\right)\right)}{NatToReal\left(multiplicity\left(card\left(a\right), a\right)\right)}}\right), normalizedResidual\left(a, blank, U, x, r\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.prefix_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Representative independence identifies every actual legal prefix. Removing the initial scale gives the square root of the ratio of the remaining and total multiplicities.

**Theorem 1.18 (normalized_letter_of_mem).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \left(r \le a \land r \ne 0\right) \Rightarrow \left(\forall i \in A,\; i \in r \Rightarrow letter\left(blank, U, i, normalizedResidual\left(a, blank, U, x, r\right)\right) = smul\left(ofReal\left(\sqrt{\frac{NatToReal\left(count\left(r, i\right)\right)}{NatToReal\left(card\left(r\right)\right)}}\right), normalizedResidual\left(a, blank, U, x, erase\left(r, i\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_letter_of_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero remaining occupation, the existing legal residual transition and multiplicity erase identity give sqrt(count(i)/card(r)) times the erased normalized residual.

**Theorem 1.19 (normalized_letter_of_not_mem).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \left(r \le a \land r \ne 0\right) \Rightarrow \left(\forall i \in A,\; \neg {i \in r} \Rightarrow letter\left(blank, U, i, normalizedResidual\left(a, blank, U, x, r\right)\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_letter_of_not_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero remaining occupation, an absent symbol has zero image. No emission rule is imposed at the terminal residual.

## Identification with the concrete padding circuit

In this section A is finite and nonempty with decidable equality, and a is any multiset on A. The head is maximalHead(a), whose capacity is the maximum of a.count. The actual memory index is Fin(proposedDimension(a)); proposedDimension is the product of (a.count(i)+1) minus the maximum count. physicalResidual(a,r) is C's existing paddingResidual embedded by physicalMemoryEquiv(a), physicalGate(a) is C's fixed unitary, and physicalFinal(a) is its sink basis vector of norm one. These are the existing concrete vectors and gate.

physicalInitial(a) names exactly the inverse sqrt(M(a)) times physicalResidual(a,a) already used by C's output theorem. The formulas below use no output or vector-identity hypothesis. The output is proved from C's positive-tail, absent-letter and tail-free steps. The identification compares actual suffix outputs and uses the existing isometric suffix injectivity, so it fixes phase as well as norm.

**Definition 1.20 (physicalInitial).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; physicalInitial\left(a\right) = smul\left(inv\left(ofReal\left(residualScale\left(a\right)\right)\right), physicalResidual\left(a, a\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physicalInitial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is a vector in the same Space(Fin(proposedDimension(a))); no second normalized family is defined.

**Theorem 1.21 (physical_residual_step).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; \left(r \le a \land r \ne 0\right) \Rightarrow \left(\forall i \in A,\; \forall k \in Fin\left(proposedDimension\left(a\right)\right),\; physicalGate\left(a\right)\left(blankMemory\left(maximalHead\left(a\right), physicalResidual\left(a, r\right)\right)\right)\left(pair\left(i, k\right)\right) = ite\left(i \in r, physicalResidual\left(a, erase\left(r, i\right)\right)\left(k\right), 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_residual_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assemble the already-proved step branches for every legal nonterminal residual.

**Theorem 1.22 (physical_initial_output).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in Fin\left(proposedDimension\left(a\right)\right),\; circuit\left(t:\mathbb{N} \mapsto physicalGate\left(a\right), card\left(a\right), 0, initialized\left(maximalHead\left(a\right), card\left(a\right), physicalInitial\left(a\right)\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot physicalFinal\left(a\right)\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_initial_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C's genuine all-word circuit output supplies the physical hypothesis used by B's residual theory.

**Theorem 1.23 (physical_scaled_initial).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; scaledInitial\left(a, physicalInitial\left(a\right)\right) = physicalResidual\left(a, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_scaled_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive scale cancels its inverse, including the all-zero occupation.

**Theorem 1.24 (physical_residual_identification).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; r \le a \Rightarrow residualMemory\left(a, maximalHead\left(a\right), physicalGate\left(a\right), physicalInitial\left(a\right), r\right) = physicalResidual\left(a, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_residual_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

B's prefix-derived residual is exactly C's chosen physicalResidual for every r less than or equal to a.

**Theorem 1.25 (physical_normalized_identification).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; r \le a \Rightarrow normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), physicalInitial\left(a\right), r\right) = smul\left(inv\left(ofReal\left(residualScale\left(r\right)\right)\right), physicalResidual\left(a, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing B normalizedResidual at these concrete parameters equals the scalar-normalized C vector.

**Theorem 1.26 (physical_prefix_identification).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; r \le a \Rightarrow \left(\forall u \in List\left(A\right),\; toMultiset\left(u\right) = a - r \Rightarrow prefixMemory\left(maximalHead\left(a\right), physicalGate\left(a\right), u, physicalResidual\left(a, a\right)\right) = physicalResidual\left(a, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_prefix_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every ordered prefix of occupation a minus r has the same actual residual, with the unscaled C initial.

**Theorem 1.27 (physical_prefix_normalized).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; r \le a \Rightarrow \left(\forall u \in List\left(A\right),\; toMultiset\left(u\right) = a - r \Rightarrow prefixMemory\left(maximalHead\left(a\right), physicalGate\left(a\right), u, physicalInitial\left(a\right)\right) = smul\left(ofReal\left(\sqrt{\frac{NatToReal\left(multiplicity\left(card\left(r\right), r\right)\right)}{NatToReal\left(multiplicity\left(card\left(a\right), a\right)\right)}}\right), smul\left(inv\left(ofReal\left(residualScale\left(r\right)\right)\right), physicalResidual\left(a, r\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_prefix_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the unit initial, the exact prefix multiplier is sqrt(M(r)/M(a)), embedded in the complex numbers.

**Theorem 1.28 (physical_normalized_norm).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; r \le a \Rightarrow norm\left(smul\left(inv\left(ofReal\left(residualScale\left(r\right)\right)\right), physicalResidual\left(a, r\right)\right)\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identification transfers B's norm theorem using the proved output and C's unit final memory.

**Theorem 1.29 (physical_initial_norm).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; norm\left(physicalInitial\left(a\right)\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_initial_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize the preceding actual-vector norm at r equal to a.

**Theorem 1.30 (physical_normalized_zero).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), physicalInitial\left(a\right), 0\right) = physicalFinal\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terminal scale is one and the identified terminal residual is exactly the common final memory.

**Theorem 1.31 (physical_head_singleton_le).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; 0 < sup\left(univ, count\left(a\right)\right) \Rightarrow singleton\left(maximalHead\left(a\right)\right) \le a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_head_singleton_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive maximum capacity implies head membership via maximal_head_spec; it is not assumed.

**Theorem 1.32 (physical_normalized_head).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; 0 < sup\left(univ, count\left(a\right)\right) \Rightarrow normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), physicalInitial\left(a\right), 0\right) = normalizedResidual\left(a, maximalHead\left(a\right), physicalGate\left(a\right), physicalInitial\left(a\right), singleton\left(maximalHead\left(a\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_head` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The legal head singleton has zero tail and multiplicity one. Both normalized vectors equal physicalFinal(a).

**Theorem 1.33 (physical_normalized_letter).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall r \in Multiset\left(A\right),\; \left(r \le a \land r \ne 0\right) \Rightarrow \left(\forall i \in A,\; letter\left(maximalHead\left(a\right), physicalGate\left(a\right), i, smul\left(inv\left(ofReal\left(residualScale\left(r\right)\right)\right), physicalResidual\left(a, r\right)\right)\right) = ite\left(i \in r, smul\left(ofReal\left(\sqrt{\frac{NatToReal\left(count\left(r, i\right)\right)}{NatToReal\left(card\left(r\right)\right)}}\right), smul\left(inv\left(ofReal\left(residualScale\left(erase\left(r, i\right)\right)\right)\right), physicalResidual\left(a, erase\left(r, i\right)\right)\right)\right), 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_letter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewrite the identified actual family and directly reuse B's existing square-root coefficient and absent-letter theorems.

All statements retain zero and mixed capacities. The all-zero initial equals the unit final vector in C's existing dimension-one branch. The emission equation requires r nonzero; the head-singleton equation requires positive maximum capacity. NormalizedGram uses this exact identified family to prove full generated span and positive-maximum nonterminal span in the physical memory.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.multiplicity_ne_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalizedResidual`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_initial`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_letter_of_mem`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_letter_of_not_mem`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_norm`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physicalInitial`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_head_singleton_le`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_initial_norm`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_initial_output`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_head`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_identification`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_letter`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_norm`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_normalized_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_prefix_identification`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_prefix_normalized`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_residual_identification`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_residual_step`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.physical_scaled_initial`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.prefix_inner_sum`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.prefix_normalized`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.residualScale`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.residual_inner_self`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.residual_norm_sq`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_ne_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_normalized`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_pos`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_sq`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.scale_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.sourceMoment`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.source_moment_zero`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PhysicalGram](PhysicalGram.md)
