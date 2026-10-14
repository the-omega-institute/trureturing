# Completely useless channels and concatenation

## Abstract

Two qubit channels are entanglement breaking before and after each switch branch, while the minus switch branch of their concatenation is not entanglement breaking.

**Definition 1.1 (Kraus normalization).**

$$\forall iota \in \operatorname{Type},\; [\operatorname{Fintype}\left(iota\right)] \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{IsKrausChannel}\left(K\right) \Leftrightarrow (\sum_{i:iota} (\operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(i\right)\right) * K\left(i\right)) = 1)$$

*Formalization.* `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.IsKrausChannel` (`✓ std3`).

*Citation.* A. Mitra; H. Badhani; S. Ghosh (2023). *Improvement in quantum communication using quantum switch*. DOI: [10.1088/1402-4896/acbcf7](https://doi.org/10.1088/1402-4896/acbcf7). URL: <https://arxiv.org/abs/2108.14001>.

*Commentary.*

Section II.A, PDF p. 2, gives the completeness identity for a channel's Kraus operators. Matrices have indices Fin 2 and complex entries; the sum is over the finite index type iota. conjTranspose is conjugate transpose.

**Definition 1.2 (The plus switch branch).**

$$\forall iota \in \operatorname{Type},\; [\operatorname{Fintype}\left(iota\right)] \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{switchPlus}\left(K\right) = \operatorname{MatrixMap}.\operatorname{of}_{kraus}\left((\operatorname{fun} (p: iota \times iota) \mapsto (\frac{1}{2}:\mathbb{C}) \cdot (K\left(p.1\right) * K\left(p.2\right) + K\left(p.2\right) * K\left(p.1\right))), (\operatorname{fun} (p: iota \times iota) \mapsto (\frac{1}{2}:\mathbb{C}) \cdot (K\left(p.1\right) * K\left(p.2\right) + K\left(p.2\right) * K\left(p.1\right)))\right)$$

*Formalization.* `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.switchPlus` (`✓ std3`).

*Citation.* A. Mitra; H. Badhani; S. Ghosh (2023). *Improvement in quantum communication using quantum switch*. DOI: [10.1088/1402-4896/acbcf7](https://doi.org/10.1088/1402-4896/acbcf7). URL: <https://arxiv.org/abs/2108.14001>.

*Commentary.*

Section II.C, Eq. (8), PDF p. 4, gives the anticommutator branch. The Kraus operator for p is one half of K(p.1)K(p.2)+K(p.2)K(p.1). The two identical arguments of MatrixMap.of_kraus produce the map X ↦ ∑p Kp X Kpᴴ. The branch is completely positive and need not preserve trace.

**Definition 1.3 (The minus switch branch).**

$$\forall iota \in \operatorname{Type},\; [\operatorname{Fintype}\left(iota\right)] \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{switchMinus}\left(K\right) = \operatorname{MatrixMap}.\operatorname{of}_{kraus}\left((\operatorname{fun} (p: iota \times iota) \mapsto (\frac{1}{2}:\mathbb{C}) \cdot (K\left(p.1\right) * K\left(p.2\right) - K\left(p.2\right) * K\left(p.1\right))), (\operatorname{fun} (p: iota \times iota) \mapsto (\frac{1}{2}:\mathbb{C}) \cdot (K\left(p.1\right) * K\left(p.2\right) - K\left(p.2\right) * K\left(p.1\right)))\right)$$

*Formalization.* `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.switchMinus` (`✓ std3`).

*Citation.* A. Mitra; H. Badhani; S. Ghosh (2023). *Improvement in quantum communication using quantum switch*. DOI: [10.1088/1402-4896/acbcf7](https://doi.org/10.1088/1402-4896/acbcf7). URL: <https://arxiv.org/abs/2108.14001>.

*Commentary.*

Section II.C, Eq. (8), PDF p. 4, gives the commutator branch. The Kraus operator for p is one half of K(p.1)K(p.2)−K(p.2)K(p.1). The two identical MatrixMap.of_kraus arguments give the coefficient one quarter in the map's action.

**Definition 1.4 (Complete uselessness).**

$$\forall iota \in \operatorname{Type},\; [\operatorname{Fintype}\left(iota\right)] \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{CompletelyUseless}\left(K\right) \Leftrightarrow ((\operatorname{IsEB}\left(\operatorname{MatrixMap}.\operatorname{of}_{kraus}\left(K, K\right)\right)) \land ((\operatorname{IsEB}\left(\operatorname{switchPlus}\left(K\right)\right)) \land (\operatorname{IsEB}\left(\operatorname{switchMinus}\left(K\right)\right))))$$

*Formalization.* `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.CompletelyUseless` (`✓ std3`).

*Citation.* A. Mitra; H. Badhani; S. Ghosh (2023). *Improvement in quantum communication using quantum switch*. DOI: [10.1088/1402-4896/acbcf7](https://doi.org/10.1088/1402-4896/acbcf7). URL: <https://arxiv.org/abs/2108.14001>.

*Commentary.*

Section III.B, PDF p. 8: “A useless channel is completely useless if under both C+ and C− it remains useless.” Uselessness means entanglement breaking. IsEB is the matrix-map predicate requiring separable output from every positive amplified input. The first conjunct includes the original channel; the other two include both switch branches.

**Definition 1.5 (Concatenated Kraus family).**

$$\forall iota \in \operatorname{Type},\; \forall kappa \in \operatorname{Type},\; \forall L \in kappa \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{composeKraus}\left(L, K\right) = \operatorname{fun} (p: iota \times kappa) \mapsto L\left(p.2\right) * K\left(p.1\right)$$

*Formalization.* `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.composeKraus` (`✓ std3`).

*Citation.* A. Mitra; H. Badhani; S. Ghosh (2023). *Improvement in quantum communication using quantum switch*. DOI: [10.1088/1402-4896/acbcf7](https://doi.org/10.1088/1402-4896/acbcf7). URL: <https://arxiv.org/abs/2108.14001>.

*Commentary.*

Section III.B uses concatenation Λ2 ◦ Λ1. The first family K acts first and L acts second, so the pair (i,j) has Kraus operator L(j)K(i). The product index type preserves all terms.

**Definition 1.6 (Conjecture 1).**

$$claim \Leftrightarrow (\forall iota \in \operatorname{Type},\; \forall kappa \in \operatorname{Type},\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{Fintype}\left(kappa\right)] \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall L \in kappa \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{IsKrausChannel}\left(K\right)) \Rightarrow ((\operatorname{IsKrausChannel}\left(L\right)) \Rightarrow ((\operatorname{CompletelyUseless}\left(K\right)) \Rightarrow ((\operatorname{CompletelyUseless}\left(L\right)) \Rightarrow (\operatorname{CompletelyUseless}\left(\operatorname{composeKraus}\left(L, K\right)\right))))))$$

*Formalization.* `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.claim` (`✓ std3`).

*Citation.* A. Mitra; H. Badhani; S. Ghosh (2023). *Improvement in quantum communication using quantum switch*. DOI: [10.1088/1402-4896/acbcf7](https://doi.org/10.1088/1402-4896/acbcf7). URL: <https://arxiv.org/abs/2108.14001>.

*Commentary.*

Section III.B, Conjecture 1, PDF p. 8: “Concatenation of two completely useless channels is always completely useless.” Both finite Kraus families are normalized qubit channels and completely useless in the sense above. The assertion ranges over every pair of finite index types and every such pair of families, and concludes complete uselessness of L after K.

**Theorem 1.7 (Conjecture 1 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mitra-badhani-ghosh-2023-completely-useless-concatenation` (refuted) by `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mitra-badhani-ghosh-2023-completely-useless-concatenation","declaration_gid":"D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Mitra; H. Badhani; S. Ghosh (2023). *Improvement in quantum communication using quantum switch*. DOI: [10.1088/1402-4896/acbcf7](https://doi.org/10.1088/1402-4896/acbcf7). URL: <https://arxiv.org/abs/2108.14001>.

*Commentary.*

At eta = 24/25, take dephasing axes z and (4/5,0,3/5), mixed with depolarization. The Kraus weights are 7/10, 1/10, 1/10 and 7/10. Six eight-term positive measure-and-prepare decompositions establish entanglement breaking of the factors and all their switch branches. For the concatenation's minus branch, the partial transpose of the unnormalized Choi matrix has quadratic value −2185891/39062500 at (−2,−1,−1,2). Every separable matrix has positive semidefinite partial transpose, so this branch is not entanglement breaking. No statement about classical capacity or perfect deterministic transmission follows.

## References

- Truth anchor: `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.CompletelyUseless`
- Truth anchor: `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.IsKrausChannel`
- Truth anchor: `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.composeKraus`
- Truth anchor: `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.result`
- Truth anchor: `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.switchMinus`
- Truth anchor: `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.switchPlus`
- Dependency: [D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation](../Quantum/Measurement/KvashchukMulticopyDesignRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](../Quantum/QuantumChannels/IptPptSquaredEquivalence.md)
- Dependency: [D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness](PauliThreeWeightBayesianInverseUniqueness.md)
