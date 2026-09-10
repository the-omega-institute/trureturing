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

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.multiplicity_ne_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalizedResidual`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_initial`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_letter_of_mem`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_letter_of_not_mem`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_norm`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/NormalizedResiduals.normalized_zero`
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
