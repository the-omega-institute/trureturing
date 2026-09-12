# Physical Stationary Gram

## Abstract

Actual fixed-unitary residual memories give the stationary memory dimension lower bound.

A and K are finite types. Space(K) is the complex Euclidean space with coordinate set K, and Unitary(A times K) consists of its linear isometric automorphisms on the joint alphabet and memory space. A fixed blank symbol embeds each memory into that joint space. Applying the same U after each embedding defines emission, a linear isometry. The coordinate slice at symbol i is the linear map letter(blank,U,i).

**Theorem 1.1 (circuit_fixed_coefficients).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \Rightarrow \left(\forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall x \in Space\left(K\right),\; \forall w \in Fin\left(n\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, n, t, initialized\left(blank, n, x\right), pair\left(w, k\right)\right) = prefixMemory\left(blank, U, ListOfFn\left(w\right), x\right)\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.circuit_fixed_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The schedule is the constant function t mapped to U. For every length and starting time, the circuit coefficient is obtained by applying the letter maps in the order of the word. This follows by induction on the word length and expansion in the memory coordinate basis.

An occupation is a multiset a on A. Its multiplicity is the number of words with that occupation. sectorVector(a.card,a) has coefficient the reciprocal square root of this multiplicity on those words and zero elsewhere. The output equation below requires that every word coefficient factor through one common final memory f. Its schedule is explicitly constant.

scaledInitial multiplies x by the square root of the multiplicity of a. residualMemory(a,blank,U,x,r) applies a representative prefix of occupation a minus r to this scaled vector. These residuals are unnormalized. For legal r, every suffix of occupation r produces f and every other suffix of the same length produces zero. The remaining circuit is isometric and therefore injective.

**Theorem 1.2 (residual_representative_independent).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; r \le a \Rightarrow \left(\forall u \in List\left(A\right),\; toMultiset\left(u\right) = a - r \Rightarrow prefixMemory\left(blank, U, u, scaledInitial\left(a, x\right)\right) = residualMemory\left(a, blank, U, x, r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_representative_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every legal prefix with the same remaining occupation gives exactly the same scaled residual vector. Equality is vector equality and includes its phase.

**Theorem 1.3 (residual_zero).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow residualMemory\left(a, blank, U, x, 0\right) = f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With no remaining symbols, the scaled residual is precisely the common final memory.

**Theorem 1.4 (residual_letter_of_mem).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; r \le a \Rightarrow \left(\forall i \in A,\; i \in r \Rightarrow letter\left(blank, U, i, residualMemory\left(a, blank, U, x, r\right)\right) = residualMemory\left(a, blank, U, x, erase\left(r, i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_letter_of_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A symbol present in the remaining occupation sends its residual to the residual with one copy of that symbol erased.

**Theorem 1.5 (residual_letter_of_not_mem).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in Multiset\left(A\right),\; \left(r \le a \land r \ne 0\right) \Rightarrow \left(\forall i \in A,\; \neg {i \in r} \Rightarrow letter\left(blank, U, i, residualMemory\left(a, blank, U, x, r\right)\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_letter_of_not_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero remaining occupation, a symbol absent from it has zero letter image.

For r in TailBox(a.count), boxOccupation(a,r) is the multiset whose counts are the coordinate values of r. occupationGram is the Gram matrix of the corresponding scaled residualMemory vectors, using the complex inner product conjugate-linear in its first argument. Thus it is the scaled matrix B.

**Theorem 1.6 (occupation_gram_psd).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; PosSemidef\left(occupationGram\left(a, blank, U, x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.occupation_gram_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Gram matrix of complex vectors is positive semidefinite, independently of the output equation.

**Theorem 1.7 (occupation_gram_rank_le).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; rank\left(occupationGram\left(a, blank, U, x\right)\right) \le FintypeCard\left(K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.occupation_gram_rank_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factoring through the memory coordinates bounds the Gram rank by the cardinality of K.

**Theorem 1.8 (occupation_gram_zero).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(norm\left(f\right) = 1 \Rightarrow occupationGram\left(a, blank, U, x\right)\left(0, 0\right) = 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.occupation_gram_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output equation and unit norm of f make the zero entry equal to one.

**Theorem 1.9 (occupation_gram_recurrence).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right) \Rightarrow \left(\forall r \in TailBox\left(i:A \mapsto count\left(a, i\right)\right),\; \forall s \in TailBox\left(i:A \mapsto count\left(a, i\right)\right),\; \left(r \ne 0 \land s \ne 0\right) \Rightarrow occupationGram\left(a, blank, U, x\right)\left(r, s\right) = \sum_{i:A}{ite\left(0 < val\left(r\left(i\right)\right) \land 0 < val\left(s\left(i\right)\right), occupationGram\left(a, blank, U, x\right)\left(lower\left(i:A \mapsto count\left(a, i\right), i, r\right), lower\left(i:A \mapsto count\left(a, i\right), i, s\right)\right), 0\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.occupation_gram_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The emission isometry preserves inner products. Summing over its letter coordinates and using the present and absent symbol identities gives the displayed recurrence on nonzero indices. The function ite chooses its second argument when its condition holds and its third argument otherwise.

**Theorem 1.10 (stationary_memory_dimension_lower_bound).**

$$\forall A \in Type,\; \forall K \in Type,\; \left(\left(Fintype\left(A\right) \land Fintype\left(K\right)\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall blank \in A,\; \forall U \in Unitary\left(Product\left(A, K\right)\right),\; \forall x \in Space\left(K\right),\; \forall f \in Space\left(K\right),\; \left(norm\left(x\right) = 1 \land \left(norm\left(f\right) = 1 \land \left(\forall w \in Fin\left(card\left(a\right)\right) \to A,\; \forall k \in K,\; circuit\left(t:\mathbb{N} \mapsto U, card\left(a\right), 0, initialized\left(blank, card\left(a\right), x\right), pair\left(w, k\right)\right) = sectorVector\left(card\left(a\right), a, w\right) \cdot f\left(k\right)\right)\right)\right) \Rightarrow \prod_{i:A}{count\left(a, i\right) + 1} - FinsetSup\left(univ\left(A\right), i:A \mapsto count\left(a, i\right)\right) \le FintypeCard\left(K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PhysicalGram.stationary_memory_dimension_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The PSD recurrence and unit zero entry give the product-minus-supremum rank bound. The Gram rank is at most the memory dimension. For zero occupation, the unit initial vector ensures a nonempty memory coordinate set, giving the same bound. Neither the common final vector nor the blank symbol is prescribed beyond the displayed hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.circuit_fixed_coefficients`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.occupation_gram_psd`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.occupation_gram_rank_le`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.occupation_gram_recurrence`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.occupation_gram_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_letter_of_mem`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_letter_of_not_mem`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_representative_independent`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.residual_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PhysicalGram.stationary_memory_dimension_lower_bound`
- Dependency: [D5/S3/Quantum/Entanglement/SequentialRegisterCircuit](../Entanglement/SequentialRegisterCircuit.md)
- Dependency: [D5/S3/Quantum/StationaryGram/StationaryOccupationRankNullity](../StationaryGram/StationaryOccupationRankNullity.md)
