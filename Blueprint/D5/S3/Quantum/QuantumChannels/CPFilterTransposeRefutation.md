# A qutrit obstruction to CP-filter equivalence with the channel transpose

## Abstract

A unital measure-and-prepare channel on three-dimensional complex matrices has diagonal transpose range and noncommuting original range. Complete positivity of a map and its inverse forces an invertible congruence, which cannot identify these ranges.

**Definition 1.1 (Invertibility with a completely positive inverse).**

$$\forall F : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \operatorname{CPInvertible}\left(F\right) \iff ((\operatorname{IsCompletelyPositive}\left(F\right)) \land (\exists G : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), (\operatorname{IsCompletelyPositive}\left(G\right)) \land ((\forall X : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), G\left(F\left(X\right)\right) = X) \land (\forall X : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), F\left(G\left(X\right)\right) = X))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.CPInvertible` (`✓ std3`).

*Citation.* Samuel A. Márquez González (2026). *Feasibility Ordering of Entanglement-Source Placement for Qubit Channels*. DOI: [10.48550/arXiv.2609.18803](https://doi.org/10.48550/arXiv.2609.18803). URL: <https://arxiv.org/abs/2609.18803v1>.

*Commentary.*

MatrixMap(Fin 3, Fin 3, complex) is the type of complex linear maps on 3 by 3 matrices. IsCompletelyPositive is the existing all-amplification predicate: for every natural n, the tensor product with the identity on Fin n maps every positive semidefinite matrix to a positive semidefinite matrix. Both inverse identities hold on every matrix. The maps need not preserve trace. PDF p. 5, Section VI, Eq. (47): “This separates the higher-dimensional problem into two levels. The strong question is whether every unital qudit channel Υ is CP-filter equivalent to its transpose, i.e., whether there exist invertible CP maps ℒ and ℛ, with CP inverses, such that Υᵀ = ℒ ∘ Υ ∘ ℛ.”

**Definition 1.2 (Unital qutrit channels).**

$$\forall F : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \operatorname{UnitalChannel}\left(F\right) \iff (((\operatorname{IsCompletelyPositive}\left(F\right)) \land (\forall X : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \operatorname{trace}\left(F\left(X\right)\right) = \operatorname{trace}\left(X\right))) \land (F\left(1\right) = 1))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.UnitalChannel` (`✓ std3`).

*Citation.* Samuel A. Márquez González (2026). *Feasibility Ordering of Entanglement-Source Placement for Qubit Channels*. DOI: [10.48550/arXiv.2609.18803](https://doi.org/10.48550/arXiv.2609.18803). URL: <https://arxiv.org/abs/2609.18803v1>.

*Commentary.*

PDF p. 2, Section II.A: “Consider completely positive trace-preserving (CPTP) maps”. PDF p. 3, Lemma 2: the scaled channel “is trace preserving and unital.” IsCPTP is the existing conjunction of all-amplification complete positivity and preservation of the matrix trace on every matrix; unitality is F(1)=1. The displayed conjunction expands that reused predicate. The carrier here is Fin 3, the qutrit instance of the dimensional question.

**Definition 1.3 (The strong question at dimension three).**

$$claim \iff (\forall F : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), (\operatorname{UnitalChannel}\left(F\right)) \implies (\forall S : Type, [\operatorname{Fintype}\left(S\right)] \forall K : S \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), (F = \operatorname{ofKraus}\left(K, K\right)) \implies (\exists L : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \exists R : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), (\operatorname{CPInvertible}\left(L\right)) \land ((\operatorname{CPInvertible}\left(R\right)) \land (\operatorname{ofKraus}\left((\lambda i : S, \operatorname{transpose}\left(K\left(i\right)\right)), (\lambda i : S, \operatorname{transpose}\left(K\left(i\right)\right))\right) = L \circ F \circ R)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.claim` (`✓ std3`).

*Citation.* Samuel A. Márquez González (2026). *Feasibility Ordering of Entanglement-Source Placement for Qubit Channels*. DOI: [10.48550/arXiv.2609.18803](https://doi.org/10.48550/arXiv.2609.18803). URL: <https://arxiv.org/abs/2609.18803v1>.

*Commentary.*

PDF p. 5, Section VI, Eq. (47): “This separates the higher-dimensional problem into two levels. The strong question is whether every unital qudit channel Υ is CP-filter equivalent to its transpose, i.e., whether there exist invertible CP maps ℒ and ℛ, with CP inverses, such that Υᵀ = ℒ ∘ Υ ∘ ℛ.” F encodes Υ, and L and R encode ℒ and ℛ. The composition symbols denote composition of complex linear maps. PDF pp. 2–3, Section II.D: “Fix a qubit basis. If a CP map has Kraus representation Λ(X)=∑ᵢ Kᵢ X Kᵢ†, its channel transpose is the CP map Λᵀ(X)=∑ᵢ Kᵢᵀ X K̅ᵢ.” PDF p. 3: “This definition is independent of the chosen Kraus representation, although it depends on the underlying basis”. ofKraus denotes the Lean function MatrixMap.of_kraus. MatrixMap.of_kraus K K is literally X↦∑ᵢ Kᵢ X Kᵢ†. Applying that same operator to the transposed family gives the displayed full sum ∑ᵢ Kᵢᵀ X (Kᵢᵀ)†. Since (Kᵢᵀ)† = K̅ᵢ, this is the source's Eq. (16) form Kᵀ X K̅, in the fixed standard basis. Definition-fidelity table: CPInvertible is CP with a two-sided CP inverse; UnitalChannel is IsCPTP together with F 1 = 1; claim uses MatrixMap.of_kraus K K for the Kraus representation and MatrixMap.of_kraus on the transposed family for the channel transpose. Trace duality determines the Heisenberg map Y↦∑ᵢ Kᵢ† Y Kᵢ from F: tr(Y F(X))=tr((∑ᵢ Kᵢ† Y Kᵢ) X). Nondegeneracy of the trace pairing identifies this map for any two finite Kraus representations. Transposing its value on Xᵀ gives ∑ᵢ Kᵢᵀ X K̅ᵢ, so the channel transpose is independent of the Kraus family. This is the dimension-three instance of the universal dimensional question; a failure here refutes that question.

$\forall S : Type, [\operatorname{Fintype}\left(S\right)] \forall K : S \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), (\forall X : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \operatorname{ofKraus}\left((\lambda i : S, \operatorname{transpose}\left(K\left(i\right)\right)), (\lambda i : S, \operatorname{transpose}\left(K\left(i\right)\right))\right)\left(X\right) = \sum_{i : S} (\operatorname{transpose}\left(K\left(i\right)\right) \cdot X \cdot \operatorname{conjTranspose}\left(\operatorname{transpose}\left(K\left(i\right)\right)\right))) \land (\forall i : S, \operatorname{conjTranspose}\left(\operatorname{transpose}\left(K\left(i\right)\right)\right) = \operatorname{map}\left(K\left(i\right), star\right))$

**Theorem 1.4 (Refutation of the strong question).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/marquez-gonzalez-2026-cp-filter-transpose-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"marquez-gonzalez-2026-cp-filter-transpose-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Samuel A. Márquez González (2026). *Feasibility Ordering of Entanglement-Source Placement for Qubit Channels*. DOI: [10.48550/arXiv.2609.18803](https://doi.org/10.48550/arXiv.2609.18803). URL: <https://arxiv.org/abs/2609.18803v1>.

*Commentary.*

Take the three trace-one positive semidefinite matrices ρ₀=diag(1/2,1/3,1/6), ρ₁=[[1/6,1/12,0],[1/12,1/3,0],[0,0,1/2]], and ρ₂=[[1/3,−1/12,0],[−1/12,1/3,0],[0,0,1/3]]. They sum to the identity. The channel F(X)=∑ⱼ Xⱼⱼρⱼ is completely positive, trace preserving, and unital. Its channel transpose has diagonal range. Applying complete positivity to the unnormalized maximally entangled projector gives a positive semidefinite Choi matrix, whose spectral decomposition supplies the finite Kraus operators. The identity Kraus scalarity theorem then forces a CP map with CP inverse to be an invertible congruence X↦AXA†. Surjectivity of R would make A F(Y) A† diagonal for every Y. Commutation of these diagonal matrices, including the image of the identity, and cancellation of A and A† force ρ₀ρ₁=ρ₁ρ₀. Their commutator has entry (0,1) equal to 1/72, a contradiction. The weaker positive/CP question in Eq. (48) remains open; the source's qubit conclusions are unaffected.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.CPInvertible`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.UnitalChannel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.result`
- Dependency: [D5/S3/Quantum/Recovery/KrausLeftInverseNecessity](../Recovery/KrausLeftInverseNecessity.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
