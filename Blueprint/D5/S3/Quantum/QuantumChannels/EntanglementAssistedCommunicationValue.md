# Entanglement-assisted communication value and the output dimension

## Abstract

Shared entanglement increases communication value by at most the output dimension.

All matrix spaces are over ℂ, with Fin(d) the standard coordinate set of size d. MatrixMap(U,V,ℂ) denotes complex linear maps from square U matrices to square V matrices. The identity in a matrix equation is the identity matrix. The real part of a trace makes the protocol expressions real even for linear maps that are not channels. For channels the traces in these expressions are already real.

**Definition 1.1 (Completely positive trace-preserving maps).**

$$\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (N: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), ((\operatorname{IsChannel}\left(N\right)) \Leftrightarrow ((\operatorname{IsCompletelyPositive}\left(N\right)) \land (\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right)), (\operatorname{tr}\left(N\left(X\right)\right) = \operatorname{tr}\left(X\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.IsChannel` (`✓ std3`).

*Citation.* Eric Chitambar; Ian George; Brian Doolittle; Marius Junge (2023). *The Communication Value of a Quantum Channel*. DOI: [10.1109/TIT.2022.3218540](https://doi.org/10.1109/TIT.2022.3218540). URL: <https://arxiv.org/abs/2109.11144v1>.

*Commentary.*

A channel is completely positive and preserves the trace of every complex input matrix. No restriction to density matrices is imposed on the trace-preservation identity.

**Definition 1.2 (Classical communication value).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (h: 1 \le n), (\forall (P: (\operatorname{Fin}\left(m\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{R}))), (\operatorname{classicalCV}\left(h, P\right) = \sum_{(y: \operatorname{Fin}\left(m\right))} (\max_{(x: \operatorname{Fin}\left(n\right))} (P\left(y, x\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.classicalCV` (`✓ std3`).

*Citation.* Eric Chitambar; Ian George; Brian Doolittle; Marius Junge (2023). *The Communication Value of a Quantum Channel*. DOI: [10.1109/TIT.2022.3218540](https://doi.org/10.1109/TIT.2022.3218540). URL: <https://arxiv.org/abs/2109.11144v1>.

*Commentary.*

For n ≥ 1 and any real array P with m outputs and n inputs, the value is the sum over outputs of the largest entry over inputs. The proof h supplies n ≥ 1, so each maximum is over a nonempty finite set. The definition also permits m = 0 and does not require P to be stochastic. For a classical channel it is Eq. (Cv) of the source, the unnormalized optimal guessing probability.

**Definition 1.3 (Values of unassisted protocols).**

$$\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (N: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\forall (v: \mathbb{R}), ((v \in \operatorname{commValues}\left(N\right)) \Leftrightarrow (\exists (n: \mathbb{N}), (\exists (m: \mathbb{N}), (\exists (h: 1 \le n), ((1 \le m) \land (\exists (\rho: (\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right))), (\exists (M: (\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right))), ((\forall (x: \operatorname{Fin}\left(n\right)), ((\operatorname{PosSemidef}\left(\rho\left(x\right)\right)) \land (\operatorname{tr}\left(\rho\left(x\right)\right) = 1))) \land ((\forall (y: \operatorname{Fin}\left(m\right)), (\operatorname{PosSemidef}\left(M\left(y\right)\right))) \land ((\sum_{(y: \operatorname{Fin}\left(m\right))} (M\left(y\right)) = 1) \land (v = \operatorname{classicalCV}\left(h, (\lambda (y: \operatorname{Fin}\left(m\right)), ((\lambda (x: \operatorname{Fin}\left(n\right)), (\Re\left(\operatorname{tr}\left(M\left(y\right) \cdot N\left(\rho\left(x\right)\right)\right)\right)))))\right)))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.commValues` (`✓ std3`).

*Citation.* Eric Chitambar; Ian George; Brian Doolittle; Marius Junge (2023). *The Communication Value of a Quantum Channel*. DOI: [10.1109/TIT.2022.3218540](https://doi.org/10.1109/TIT.2022.3218540). URL: <https://arxiv.org/abs/2109.11144v1>.

*Commentary.*

A value belongs to commValues(N) precisely when some positive input and output alphabet sizes n and m, density matrices ρ(x), and a POVM M(y) induce the real array P(y|x) = Re tr(M(y) N(ρ(x))) with that classical communication value. The density matrices are positive semidefinite with trace one; the POVM elements are positive semidefinite and sum to the identity. This is the protocol optimization in Definition 1, with both finite alphabet sizes allowed to vary.

**Definition 1.4 (Unassisted communication value).**

$$\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (N: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\operatorname{commValue}\left(N\right) = \operatorname{sSup}\left(\operatorname{commValues}\left(N\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.commValue` (`✓ std3`).

*Citation.* Eric Chitambar; Ian George; Brian Doolittle; Marius Junge (2023). *The Communication Value of a Quantum Channel*. DOI: [10.1109/TIT.2022.3218540](https://doi.org/10.1109/TIT.2022.3218540). URL: <https://arxiv.org/abs/2109.11144v1>.

*Commentary.*

The real supremum sSup of the set of unassisted protocol values is commValue(N), written cv(N). For a channel this is the communication value of Definition 1, including the supremum over both finite alphabet sizes. The definition itself is given for every complex linear map and every natural input and output dimension.

**Definition 1.5 (Values of entanglement-assisted protocols).**

$$\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (N: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\forall (v: \mathbb{R}), ((v \in \operatorname{eaCommValues}\left(N\right)) \Leftrightarrow (\exists (c: \mathbb{N}), (\exists (r: \mathbb{N}), (\exists (n: \mathbb{N}), (\exists (m: \mathbb{N}), (\exists (h: 1 \le n), ((1 \le m) \land (\exists (\phi: \operatorname{Matrix}\left((\operatorname{Fin}\left(c\right)\times\operatorname{Fin}\left(r\right)), (\operatorname{Fin}\left(c\right)\times\operatorname{Fin}\left(r\right)), \mathbb{C}\right)), (\exists (E: (\operatorname{Fin}\left(n\right) \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(c\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right))), (\exists (M: (\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(b\right)\times\operatorname{Fin}\left(r\right)), (\operatorname{Fin}\left(b\right)\times\operatorname{Fin}\left(r\right)), \mathbb{C}\right))), (((\operatorname{PosSemidef}\left(\phi\right)) \land (\operatorname{tr}\left(\phi\right) = 1)) \land ((\forall (x: \operatorname{Fin}\left(n\right)), (\operatorname{IsChannel}\left(E\left(x\right)\right))) \land ((\forall (y: \operatorname{Fin}\left(m\right)), (\operatorname{PosSemidef}\left(M\left(y\right)\right))) \land ((\sum_{(y: \operatorname{Fin}\left(m\right))} (M\left(y\right)) = 1) \land (v = \operatorname{classicalCV}\left(h, (\lambda (y: \operatorname{Fin}\left(m\right)), ((\lambda (x: \operatorname{Fin}\left(n\right)), (\Re\left(\operatorname{tr}\left(M\left(y\right) \cdot \operatorname{kron}\left((N \circ E\left(x\right)), \operatorname{id}\left(\operatorname{Fin}\left(r\right), \mathbb{C}\right)\right)\left(\phi\right)\right)\right)))))\right)))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.eaCommValues` (`✓ std3`).

*Citation.* Eric Chitambar; Ian George; Brian Doolittle; Marius Junge (2023). *The Communication Value of a Quantum Channel*. DOI: [10.1109/TIT.2022.3218540](https://doi.org/10.1109/TIT.2022.3218540). URL: <https://arxiv.org/abs/2109.11144v1>.

*Commentary.*

The shared density matrix φ acts on dimensions c and r. For each input x, a channel E(x) maps the c-dimensional sender system into the a-dimensional channel input. The receiver measures a POVM on the channel output together with the r-dimensional shared system. The symbol kron denotes the tensor product of linear maps, and id is the identity map on matrices of the indicated coordinate type. The induced array is P(y|x) = Re tr(M(y) ((N∘E(x))⊗id)(φ)). Its classical communication value is the protocol value. The natural dimensions c and r are unrestricted, and n and m are positive. These are the protocols of Eq. (Ea-cv); no fixed bound on shared entanglement is imposed.

**Definition 1.6 (Entanglement-assisted communication value).**

$$\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (N: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\operatorname{eaCommValue}\left(N\right) = \operatorname{sSup}\left(\operatorname{eaCommValues}\left(N\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.eaCommValue` (`✓ std3`).

*Citation.* Eric Chitambar; Ian George; Brian Doolittle; Marius Junge (2023). *The Communication Value of a Quantum Channel*. DOI: [10.1109/TIT.2022.3218540](https://doi.org/10.1109/TIT.2022.3218540). URL: <https://arxiv.org/abs/2109.11144v1>.

*Commentary.*

The real supremum sSup of all assisted protocol values is eaCommValue(N), written cv*(N). The set includes all finite shared dimensions, all shared density matrices, all finite positive alphabet sizes, local encoding channels and joint decoding POVMs. This restates the assisted communication value defined after Eq. (Ea-cv). As with commValue, the definition is also available for arbitrary complex linear maps and natural dimensions.

**Definition 1.7 (The output-dimension comparison).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), ((1 \le a) \Rightarrow ((1 \le b) \Rightarrow (\forall (N: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), ((\operatorname{IsChannel}\left(N\right)) \Rightarrow (\operatorname{eaCommValue}\left(N\right) \le (b: \mathbb{R}) \cdot \operatorname{commValue}\left(N\right))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.claim` (`✓ std3`).

*Citation.* Eric Chitambar; Ian George; Brian Doolittle; Marius Junge (2023). *The Communication Value of a Quantum Channel*. DOI: [10.1109/TIT.2022.3218540](https://doi.org/10.1109/TIT.2022.3218540). URL: <https://arxiv.org/abs/2109.11144v1>.

*Commentary.*

For every pair of positive finite dimensions a and b and every channel from a by a matrices to b by b matrices, cv*(N) ≤ b cv(N). This is the conjecture stated in the source, with b the output dimension.

**Theorem 1.8 (Shared entanglement gives at most an output-dimension advantage).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.result` (`✓ std3`). ∎

*Resolves.* `Problems/chitambar-et-al-2023-entanglement-assisted-communication-value-bound` (proved) by `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chitambar-et-al-2023-entanglement-assisted-communication-value-bound","declaration_gid":"D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eric Chitambar; Ian George; Brian Doolittle; Marius Junge (2023). *The Communication Value of a Quantum Channel*. DOI: [10.1109/TIT.2022.3218540](https://doi.org/10.1109/TIT.2022.3218540). URL: <https://arxiv.org/abs/2109.11144v1>.

*Commentary.*

Fix a channel N and write b for its positive output dimension and J for its Choi matrix. Use tensor order A⊗B in this explanation; exchanging the factors gives the B⊗A coordinate convention of the matrix formulas. For every assisted protocol value v there is a positive semidefinite operator Ω with tr_A Ω = I_B and v = Re tr(JΩ). Choose an input maximizing each output probability and contract the corresponding encoded shared state with the receiver's POVM element. Complete positivity gives positivity of the resulting sum. Trace preservation of each encoding gives the same receiver marginal for every input; the POVM identity then gives tr_A Ω = I_B.

Depolarizing the B factor gives Ω' = (Ω + tr_B Ω ⊗ I_B)/(b+1). This operator has a finite product decomposition Ω' = ∑ₖ Pₖ⊗Qₖ with Pₖ and Qₖ positive semidefinite. To see finiteness directly, write Ω as a finite sum of rank-one positive operators |ψ⟩⟨ψ|. Choose independent coordinates zⱼ equal to zero with probability 1/2 and to each of √2, −√2, i√2, −i√2 with probability 1/8. For u_z = (I_A⊗⟨z|)ψ, the finite average of |u_z⟩⟨u_z|⊗|z⟩⟨z| is |ψ⟩⟨ψ| + tr_B(|ψ⟩⟨ψ|)⊗I_B. Summing and dividing by b+1 gives the asserted decomposition. Moreover tr_A Ω' = I_B. Since tr_B J = I_A and tr Ω = b, its objective is Re tr(JΩ') = (v+b)/(b+1).

For each product term with tₖ = tr Pₖ > 0, use the state ρₖ = Pₖᵀ/tₖ and the POVM element Mₖ = tₖQₖ; terms with zero trace contribute zero and may use any density matrix. The marginal identity makes these POVM elements sum to I_B. The resulting unassisted protocol has diagonal guessing score (v+b)/(b+1). Maximizing over inputs for each output gives a classical communication value at least this score, hence (v+b)/(b+1) ≤ cv(N).

Every output state is a density matrix, so each output's largest probability is at most tr M(y). Summing the POVM elements gives cv(N) ≤ b. Therefore v ≤ (b+1)cv(N)−b ≤ b cv(N). Taking the supremum over all assisted protocols proves claim.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.IsChannel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.classicalCV`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.commValue`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.commValues`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.eaCommValue`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.eaCommValues`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages](../Entanglement/AbsoluteSeparability/LowRankRaysAverages.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](PositiveFilterTransposeRefutation.md)
