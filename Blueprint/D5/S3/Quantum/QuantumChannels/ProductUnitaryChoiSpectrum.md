# The Choi spectrum of unital product-unitary-equivariant maps

## Abstract

For all positive n₁ and n₂, the Choi matrix of the unital map that acts on the four isotypic components of n₁n₂ × n₁n₂ matrices with weights 1, λ₀₁, λ₁₀ and λ₁₁ has its eigenvalues among four values given by explicit formulas, taken with multiplicities 1, n₁² − 1, n₂² − 1 and (n₁² − 1)(n₂² − 1); coinciding values add their multiplicities.

**Definition 1.1 (The trace-to-identity map).**

$$\forall n: \mathbb{N}, \forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{depol}\left(n\right)(X) = \frac{\operatorname{tr}\left(X\right)}{\operatorname{cast}\left(n\right)} I$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.depol` (`✓ std3`).

*Citation.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

On n × n complex matrices, D(X) = tr(X) I/n; cast denotes the inclusion of the natural numbers in ℂ. Its image is the multiples of the identity, and D is the identity there, so D is the projection onto the trivial component of the conjugation action of the unitary group.

**Definition 1.2 (The complementary projection).**

$$\forall n: \mathbb{N}, \forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{compl}\left(n\right)(X) = X - \operatorname{depol}\left(n\right)(X)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.compl` (`✓ std3`).

*Citation.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

Q(X) = X − D(X), the projection onto the trace-zero matrices.

**Definition 1.3 (The unital product-unitary-equivariant map).**

$$\forall n_1, n_2: \mathbb{N}, \forall \lambda_{01}, \lambda_{10}, \lambda_{11}: \mathbb{C}, \operatorname{phi}\left(n_1, n_2, \lambda_{01}, \lambda_{10}, \lambda_{11}\right) = \operatorname{kron}\left(\operatorname{depol}\left(n_1\right), \operatorname{depol}\left(n_2\right)\right) + \lambda_{01} \operatorname{kron}\left(\operatorname{depol}\left(n_1\right), \operatorname{compl}\left(n_2\right)\right) + \lambda_{10} \operatorname{kron}\left(\operatorname{compl}\left(n_1\right), \operatorname{depol}\left(n_2\right)\right) + \lambda_{11} \operatorname{kron}\left(\operatorname{compl}\left(n_1\right), \operatorname{compl}\left(n_2\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.phi` (`✓ std3`).

*Citation.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

The map Φ on n₁n₂ × n₁n₂ complex matrices with weight 1 on D ⊗ D and weights λ₀₁, λ₁₀, λ₁₁ on D ⊗ Q, Q ⊗ D and Q ⊗ Q. The tensor product of maps is the frozen kron of D5/S3/Quantum/Foundation/FiniteKrausChannel. Φ is unital, and it commutes with conjugation by U ⊗ V for unitary U and V; for n₁, n₂ ≥ 2 every unital map with this symmetry has this form, and it preserves Hermiticity exactly when the weights are real. On matrix units, with a = (1 − λ₀₁ − λ₁₀ + λ₁₁)/(n₁n₂), b = (λ₀₁ − λ₁₁)/n₁, c = (λ₁₀ − λ₁₁)/n₂ and d = λ₁₁, Φ(E_ij ⊗ F_kl) = a δ_ij δ_kl I + b δ_ij I ⊗ F_kl + c δ_kl E_ij ⊗ I + d E_ij ⊗ F_kl.

**Definition 1.4 (The diagonal pair vector).**

$$\forall n: \mathbb{N}, \forall i, j: \operatorname{Fin}\left(n\right), \operatorname{omega}\left(n\right)(i, j) = [i = j]$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.omega` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

The vector on the pairs (i, j) of indices in {0, …, n − 1} with entry 1 when i = j and 0 otherwise; the bracket [i = j] denotes this indicator. It is the unnormalized maximally entangled vector Σ_i e_i ⊗ e_i.

**Theorem 1.5 (The squared length of the diagonal pair vector).**

$$\forall n: \mathbb{N}, \operatorname{dotProduct}\left(\operatorname{omega}\left(n\right), \operatorname{omega}\left(n\right)\right) = \operatorname{cast}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.omega_dot_omega` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

ω has exactly n entries equal to 1 and the others 0, so ω · ω = n as a complex number.

**Definition 1.6 (The Choi matrix of the identity map).**

$$\forall n: \mathbb{N}, \operatorname{kmat}\left(n\right) = \operatorname{vecMulVec}\left(\operatorname{omega}\left(n\right), \operatorname{omega}\left(n\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.kmat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

K = ωωᵀ, the matrix on pairs with entry ω(x)ω(y) at (x, y); it is the Choi matrix Σ_{i,j} E_ij ⊗ E_ij of the identity map on n × n matrices.

**Definition 1.7 (The Choi matrix of the trace-to-identity map).**

$$\forall n: \mathbb{N}, \operatorname{dmat}\left(n\right) = \frac{1}{\operatorname{cast}\left(n\right)} I$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.dmat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

I/n on pairs of indices: the Choi matrix of depol(n).

**Definition 1.8 (The Choi matrix of the complementary projection).**

$$\forall n: \mathbb{N}, \operatorname{qmat}\left(n\right) = \operatorname{kmat}\left(n\right) - \operatorname{dmat}\left(n\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.qmat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

K − I/n: the Choi matrix of compl(n).

**Theorem 1.9 (The Choi matrix grouped by factor).**

$$\forall n_1, n_2: \mathbb{N}, \forall \lambda_{01}, \lambda_{10}, \lambda_{11}: \mathbb{C}, \operatorname{reindex}\left(prodProdProdComm, prodProdProdComm, \sum_{p,q} \operatorname{kron}\left(\operatorname{single}\left(p, q, 1\right), \operatorname{phi}\left(n_1, n_2, \lambda_{01}, \lambda_{10}, \lambda_{11}\right)(\operatorname{single}\left(p, q, 1\right))\right)\right) = \operatorname{kron}\left(\operatorname{dmat}\left(n_1\right), \operatorname{dmat}\left(n_2\right)\right) + \lambda_{01} \operatorname{kron}\left(\operatorname{dmat}\left(n_1\right), \operatorname{qmat}\left(n_2\right)\right) + \lambda_{10} \operatorname{kron}\left(\operatorname{qmat}\left(n_1\right), \operatorname{dmat}\left(n_2\right)\right) + \lambda_{11} \operatorname{kron}\left(\operatorname{qmat}\left(n_1\right), \operatorname{qmat}\left(n_2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.choi_reindex` (`✓ std3`). ∎

*Citation.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

The Choi matrix C_Φ = Σ_{p,q} E_pq ⊗ Φ(E_pq) is indexed by pairs ((p₁, p₂), (r₁, r₂)) of an input and an output index. Reindexing both sides by the regrouping prodProdProdComm, which sends ((p₁, p₂), (r₁, r₂)) to ((p₁, r₁), (p₂, r₂)), turns C_Φ into the weighted sum of Kronecker products of the single-factor Choi matrices dmat and qmat, with the weights of phi. Here kron is the Kronecker product of matrices. In the basis of I, I ⊗ K, K ⊗ I and K ⊗ K this is the Choi matrix a I + b (I ⊗ K₂) + c (K₁ ⊗ I) + d (K₁ ⊗ K₂) displayed in the source, with a = (1 − λ₀₁ − λ₁₀ + λ₁₁)/(n₁n₂), b = (λ₀₁ − λ₁₁)/n₁, c = (λ₁₀ − λ₁₁)/n₂ and d = λ₁₁.

**Definition 1.10 (The conjectured Choi spectrum).**

$$claim \Leftrightarrow (\forall n_1, n_2: \mathbb{N}, 1 \leq n_1, 1 \leq n_2 \Rightarrow \forall \lambda_{01}, \lambda_{10}, \lambda_{11}: \mathbb{C}, \operatorname{charpoly}\left(\sum_{p,q} \operatorname{kron}\left(\operatorname{single}\left(p, q, 1\right), \operatorname{phi}\left(n_1, n_2, \lambda_{01}, \lambda_{10}, \lambda_{11}\right)(\operatorname{single}\left(p, q, 1\right))\right)\right) = (X - \frac{1 + (\operatorname{cast}\left(n_2\right)^{2}-1)\lambda_{01} + (\operatorname{cast}\left(n_1\right)^{2}-1)\lambda_{10} + (\operatorname{cast}\left(n_1\right)^{2}-1)(\operatorname{cast}\left(n_2\right)^{2}-1)\lambda_{11}}{\operatorname{cast}\left(n_1\right) \operatorname{cast}\left(n_2\right)}) (X - \frac{1 + (\operatorname{cast}\left(n_2\right)^{2}-1)\lambda_{01} - \lambda_{10} - (\operatorname{cast}\left(n_2\right)^{2}-1)\lambda_{11}}{\operatorname{cast}\left(n_1\right) \operatorname{cast}\left(n_2\right)})^{n_1^{2}-1} (X - \frac{1 - \lambda_{01} + (\operatorname{cast}\left(n_1\right)^{2}-1)\lambda_{10} - (\operatorname{cast}\left(n_1\right)^{2}-1)\lambda_{11}}{\operatorname{cast}\left(n_1\right) \operatorname{cast}\left(n_2\right)})^{n_2^{2}-1} (X - \frac{1 - \lambda_{01} - \lambda_{10} + \lambda_{11}}{\operatorname{cast}\left(n_1\right) \operatorname{cast}\left(n_2\right)})^{(n_1^{2}-1)(n_2^{2}-1)})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.claim` (`✓ std3`).

*Citation.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

The conjecture of Remark V.2 of arXiv:2601.02282v1: for every n₁ and n₂, the eigenvalues of the Choi matrix C_Φ = Σ_{p,q} E_pq ⊗ Φ(E_pq) are the four values of Lemma V.8, with multiplicities 1, n₁² − 1, n₂² − 1 and (n₁² − 1)(n₂² − 1). The characteristic polynomial records the eigenvalues with their algebraic multiplicities; when two of the four values coincide their multiplicities add. The source states the formulas for n₁, n₂ ∈ {2, 3} and real weights; here n₁, n₂ ≥ 1 and the weights are complex. In the four roots the dimensions are cast to ℂ; the multiplicity exponents n₁² − 1, n₂² − 1 and (n₁² − 1)(n₂² − 1) are natural numbers.

**Theorem 1.11 (The Choi spectrum in every dimension).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. García-Velo, A. Ibort (2026). *Schwarz maps with symmetry*. DOI: [10.48550/arXiv.2601.02282](https://doi.org/10.48550/arXiv.2601.02282). URL: <https://arxiv.org/abs/2601.02282v1>.

*Commentary.*

Write ω for the vector of ℂ^n ⊗ ℂ^n with entry 1 at the pairs (i, i) and 0 elsewhere, and K = ωωᵀ. The Choi matrix of D is I/n and that of Q is K − I/n. Grouping the indices of C_Φ by factor turns it into a I + b (I ⊗ K₂) + c (K₁ ⊗ I) + d (K₁ ⊗ K₂). Let e₀ be the basis vector at the pair (0, 0) and u = ω − e₀; since e₀ᵀu = 0, the shear S = I + u e₀ᵀ has inverse I − u e₀ᵀ, sends e₀ to ω, and conjugates K to the matrix whose only nonzero row is the row of (0, 0), with diagonal entry n there. Conjugating by S₁ ⊗ S₂ makes the matrix block upper triangular for the blocks given by whether the first and the second index equals (0, 0). Each diagonal block is a multiple of the identity: of size 1 and value a + bn₂ + cn₁ + dn₁n₂, of size n₂² − 1 and value a + cn₁, of size n₁² − 1 and value a + bn₂, and of size (n₁² − 1)(n₂² − 1) and value a. Substituting a, b, c and d gives the four values of the claim.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.choi_reindex`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.compl`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.depol`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.dmat`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.kmat`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.omega`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.omega_dot_omega`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.phi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.qmat`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
