# PPT channels with product-unitary symmetry become entanglement breaking after one composition

## Abstract

For all n₁, n₂ ≥ 2 and real λ₀₁, λ₁₀, λ₁₁, if the unital map with weights 1, λ₀₁, λ₁₀ and λ₁₁ on the four isotypic components of n₁n₂ × n₁n₂ matrices has a positive semidefinite Choi matrix whose partial transpose is also positive semidefinite, then the Choi matrix of the map composed with itself is a finite sum of Kronecker products of positive semidefinite matrices across input and output.

**Definition 1.1 (The Choi matrix).**

$$\forall (\iota: Type) [\operatorname{Fintype}\left(\iota\right)] [\operatorname{DecidableEq}\left(\iota\right)], \forall \psi: \operatorname{MatrixMap}\left(\iota, \iota, \mathbb{C}\right), \operatorname{choi}\left(\psi\right) = \sum_{p,q} \operatorname{kron}\left(\operatorname{single}\left(p, q, 1\right), \psi(\operatorname{single}\left(p, q, 1\right))\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.choi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

For a finite type ι with decidable equality and a linear map ψ on square complex matrices indexed by ι, choi(ψ) = Σ_{p,q} E_pq ⊗ ψ(E_pq), a matrix indexed by pairs (input index, output index); kron is the Kronecker product of matrices and single(p, q, 1) is the matrix unit E_pq.

**Definition 1.2 (Flattening the two tensor factors).**

$$\forall n_1, n_2: \mathbb{N}, \operatorname{flat}\left(n_1, n_2\right) = \operatorname{prodCongr}\left(finProdFinEquiv, finProdFinEquiv\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.flat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

The equivalence that flattens the input pair (p₁, p₂) and the output pair (r₁, r₂) separately by Mathlib's finProdFinEquiv from Fin n₁ × Fin n₂ to Fin (n₁n₂). It turns a matrix indexed by ((p₁, p₂), (r₁, r₂)) into a matrix on Fin (n₁n₂) × Fin (n₁n₂) with the input factor first, the index type of separableCone.

**Theorem 1.3 (Composition multiplies the weights).**

$$\forall n_1, n_2: \mathbb{N}, 1 \leq n_1 \Rightarrow 1 \leq n_2 \Rightarrow \forall a, b, c, a', b', c': \mathbb{C}, \operatorname{phi}\left(n_1, n_2, a, b, c\right) \circ \operatorname{phi}\left(n_1, n_2, a', b', c'\right) = \operatorname{phi}\left(n_1, n_2, a a', b b', c c'\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.phi_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

D and Q are complementary idempotents on each factor (D ∘ D = D, D ∘ Q = Q ∘ D = 0, Q ∘ Q = Q), and the tensor product of maps is multiplicative on Kronecker products, so composing two maps of the family multiplies their weights. In particular Φ ∘ Φ has the weights λ₀₁², λ₁₀² and λ₁₁².

**Definition 1.4 (PPT² for unital product-unitary-equivariant maps).**

$$claim \Leftrightarrow (\forall n_1, n_2: \mathbb{N}, 2 \leq n_1, 2 \leq n_2 \Rightarrow \forall \lambda_{01}, \lambda_{10}, \lambda_{11}: \mathbb{R}, \operatorname{PosSemidef}\left(\operatorname{choi}\left(\operatorname{phi}\left(n_1, n_2, \operatorname{cast}\left(\lambda_{01}\right), \operatorname{cast}\left(\lambda_{10}\right), \operatorname{cast}\left(\lambda_{11}\right)\right)\right)\right) \Rightarrow \operatorname{PosSemidef}\left(\operatorname{partialTranspose}\left(\operatorname{choi}\left(\operatorname{phi}\left(n_1, n_2, \operatorname{cast}\left(\lambda_{01}\right), \operatorname{cast}\left(\lambda_{10}\right), \operatorname{cast}\left(\lambda_{11}\right)\right)\right)\right)\right) \Rightarrow \operatorname{separableCone}\left(\operatorname{reindex}\left(\operatorname{flat}\left(n_1, n_2\right), \operatorname{flat}\left(n_1, n_2\right), \operatorname{choi}\left((\operatorname{phi}\left(n_1, n_2, \operatorname{cast}\left(\lambda_{01}\right), \operatorname{cast}\left(\lambda_{10}\right), \operatorname{cast}\left(\lambda_{11}\right)\right) \circ \operatorname{phi}\left(n_1, n_2, \operatorname{cast}\left(\lambda_{01}\right), \operatorname{cast}\left(\lambda_{10}\right), \operatorname{cast}\left(\lambda_{11}\right)\right))\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

Here cast is the inclusion of ℝ in ℂ, and phi(n₁, n₂, λ₀₁, λ₁₀, λ₁₁) = D₁ ⊗ D₂ + λ₀₁ D₁ ⊗ Q₂ + λ₁₀ Q₁ ⊗ D₂ + λ₁₁ Q₁ ⊗ Q₂ is the unital map of D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum, with D(X) = tr(X) I/n and Q = id − D; for n₁, n₂ ≥ 2 these are exactly the unital, Hermiticity-preserving maps commuting with conjugation by U ⊗ V. partialTranspose transposes the output indices: (partialTranspose M)((p, r), (q, s)) = M((p, s), (q, r)). The two hypotheses say that Φ is completely positive and completely copositive (Φ is PPT). separableCone is the frozen cone of finite sums of Kronecker products A ⊗ B of positive semidefinite matrices, so the conclusion says that Φ ∘ Φ is entanglement breaking. The composition is needed: when n₁ ≠ n₂ there are PPT maps in this family that are not entanglement breaking.

**Theorem 1.5 (PPT² in every dimension).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

Since D and Q are complementary idempotents, Φ ∘ Φ has weights λ₀₁², λ₁₀² and λ₁₁². Let ω be the vector of ℂⁿ ⊗ ℂⁿ with entry 1 at the pairs (i, i), K = ωωᵀ, and D = Σ_i E_ii ⊗ E_ii. Averaging vv* ⊗ v̄v̄* over the 4ⁿ vectors v = Σ_j θ_j e_j with θ_j ∈ {1, i, −1, −i} gives I + K − D, so I + K is separable; with v replaced on the output side by its twist by the characters m ↦ ζ^{km} of the n-th roots of unity, k = 1, …, n − 1, the same average gives (n − 1)I + D − K, so nI − K = that sum + Σ_{i≠j} E_ii ⊗ E_jj is separable. Grouped by factor, the Choi matrix of Φ ∘ Φ equals Σ_{r,s} N_rs S_r ⊗ S_s with S₀ = nI − K and S₁ = I + K on each factor, and the coefficients are n₁(n₁+1)n₂(n₂+1)·N₀₀ = 1 − (n₂+1)λ₀₁² − (n₁+1)λ₁₀² + (n₁+1)(n₂+1)λ₁₁², n₁(n₁+1)n₂(n₂+1)·N₀₁ = 1 + (n₂²−1)λ₀₁² − (n₁+1)λ₁₀² − (n₁+1)(n₂²−1)λ₁₁², the mirror image N₁₀, and N₁₁ with all signs positive. Testing the Choi matrix of Φ and its partial transpose on ω₁ ⊗ ω₂, ω ⊗ e₀₁, e₀₁ ⊗ e₀₁, e₀₀ ⊗ e₀₀ and the antisymmetric vectors e₀₁ − e₁₀ gives eight linear inequalities in λ. N₁₀ ≥ 0 and N₀₁ ≥ 0 follow from polynomial identities expressing 2n₁²n₂² N times the positive constant as a sum of products of two of these inequalities with nonnegative coefficients; N₀₀ ≥ 0 follows from |λ₀₁| ≤ 1/(n₂+1) and |λ₁₀| ≤ 1/(n₁+1), which are linear consequences of the inequalities. The source proves this property for (n₁, n₂) = (2, 2) and (2, 3).

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.choi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.flat`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.phi_comp`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.result`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum](ProductUnitaryChoiSpectrum.md)
