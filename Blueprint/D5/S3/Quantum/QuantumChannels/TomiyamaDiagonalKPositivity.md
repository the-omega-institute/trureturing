# The k-positive region of the diagonal-perturbed Tomiyama maps

## Abstract

For every 2 ≤ k ≤ d, the k-positive maps of the diagonal-perturbed Tomiyama family on d × d matrices are exactly those whose parameters lie in the quadrilateral spanned by the identity, the two extremal completely positive maps and the k-positive Tomiyama map.

**Definition 1.1 (The diagonal-perturbed Tomiyama family).**

$$\operatorname{phi}\left(d, \alpha, \beta\right)(X) = (1 - \alpha - \beta) X + \frac{\alpha}{d} \operatorname{tr}\left(X\right) I + \beta \operatorname{diag}\left(X\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.phi` (`✓ std3`).

*Citation.* A. Bera, B. Bhattacharya, D. Chruściński (2026). *Tomiyama-type maps with a diagonal perturbation*. DOI: [10.48550/arXiv.2604.18600](https://doi.org/10.48550/arXiv.2604.18600). URL: <https://arxiv.org/abs/2604.18600v1>.

*Commentary.*

Φ_{α,β} = (1 − α − β) id + α τ₀ + β Δ on d × d complex matrices, where τ₀(X) = tr(X) I/d and Δ keeps the diagonal of X, as in Eq. (6) of arXiv:2604.18600v1.

**Definition 1.2 (k-positivity).**

$$\operatorname{KPositive}\left(k, d, \phi\right) \Leftrightarrow \forall Y: \operatorname{PSD}\left(k \times d\right), \operatorname{kron}\left(\operatorname{id}\left(k\right), \phi\right)(Y) \geq 0$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.KPositive` (`✓ std3`).

*Citation.* A. Bera, B. Bhattacharya, D. Chruściński (2026). *Tomiyama-type maps with a diagonal perturbation*. DOI: [10.48550/arXiv.2604.18600](https://doi.org/10.48550/arXiv.2604.18600). URL: <https://arxiv.org/abs/2604.18600v1>.

*Commentary.*

A map Φ on d × d matrices is k-positive when id_k ⊗ Φ sends every positive semidefinite kd × kd matrix to a positive semidefinite matrix. The tensor product of maps is the frozen kron of D5/S3/Quantum/Foundation/FiniteKrausChannel, with the identity on k × k matrices as the first factor.

**Definition 1.3 (The conjectured quadrilateral).**

$$\operatorname{quadrilateral}\left(d, k\right) = \operatorname{conv}\left(\{(0, 0), (0, \frac{d}{d-1}), (\frac{d}{d-1}, -\frac{1}{d-1}), (\frac{kd}{kd-1}, 0)\}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.quadrilateral` (`✓ std3`).

*Citation.* A. Bera, B. Bhattacharya, D. Chruściński (2026). *Tomiyama-type maps with a diagonal perturbation*. DOI: [10.48550/arXiv.2604.18600](https://doi.org/10.48550/arXiv.2604.18600). URL: <https://arxiv.org/abs/2604.18600v1>.

*Commentary.*

The convex hull in the (α, β) plane of the parameter points of Ψ₀ (the identity), Ψ₁ and Ψ₂ (the two completely positive vertices) and the Tomiyama map 𝒯_k, whose α is kd/(kd − 1).

**Definition 1.4 (Conjecture 2.4 for 2 ≤ k ≤ d).**

$$claim \Leftrightarrow (\forall d, k: \mathbb{N}, 2 \leq k \leq d \Rightarrow \forall \alpha, \beta: \mathbb{R}, \operatorname{KPositive}\left(k, d, \operatorname{phi}\left(d, \alpha, \beta\right)\right) \Leftrightarrow (\alpha, \beta) \in \operatorname{quadrilateral}\left(d, k\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.claim` (`✓ std3`).

*Citation.* A. Bera, B. Bhattacharya, D. Chruściński (2026). *Tomiyama-type maps with a diagonal perturbation*. DOI: [10.48550/arXiv.2604.18600](https://doi.org/10.48550/arXiv.2604.18600). URL: <https://arxiv.org/abs/2604.18600v1>.

*Commentary.*

Conjecture 2.4 of arXiv:2604.18600v1, "A set of k-positive maps Φ_{α,β} forms a quadrilateral 𝒫_k = conv{Ψ₀, Ψ₁, Ψ₂, 𝒯_k}", in the range 2 ≤ k ≤ d.

**Definition 1.5 (Fourier rows).**

$$\forall d, k: \mathbb{N}, 0 < d, k \leq d \Rightarrow \forall a: \operatorname{Fin}\left(k\right), \forall j: \operatorname{Fin}\left(d\right), \operatorname{entry}\left(\operatorname{fourierRows}\left(k, d\right), a, j\right) = \operatorname{stdAddChar}\left(\operatorname{finEquiv}\left(d, j\right) \times \operatorname{finEquiv}\left(d, \operatorname{castLE}\left(a\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.fourierRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive d and k ≤ d, the k Fourier rows have entries χ_d(ja), where χ_d is the standard additive character on the residues modulo d and a is embedded from Fin k into Fin d.

**Theorem 1.6 (Orthogonality of Fourier rows).**

$$\forall d, k: \mathbb{N}, 0 < d, k \leq d \Rightarrow \operatorname{fourierRows}\left(k, d\right) \times \operatorname{adjoint}\left(\operatorname{fourierRows}\left(k, d\right)\right) = d \times \operatorname{identity}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.fourierRows_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct Fourier rows are orthogonal, and each has squared norm d. At k = d, division by the square root of d gives a unitary Fourier matrix; conjugation gives the negative-character convention.

**Theorem 1.7 (The k-positive region is the quadrilateral).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.result` (`✓ std3`). ∎

*Resolves.* `Problems/bera-2026-tomiyama-diagonal-k-positivity` (proved) by `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bera-2026-tomiyama-diagonal-k-positivity","declaration_gid":"D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Write ‖X‖² = Σ_{i,j} |X_ij|² for the squared Frobenius norm and Q(X) = (α/d)‖X‖² + β Σ_i |X_ii|² + (1 − α − β)|tr X|². For vectors u, w in ℂ^k ⊗ ℂ^d with coefficient matrices U, W, the value of (id_k ⊗ Φ_{α,β})(ww*) on u is Q(U*W), so k-positivity means Q ≥ 0 on every U*W. Four tests give the four edges: the matrix unit E₁₂ gives α ≥ 0; E₁₁ − E₂₂, which needs k ≥ 2, gives α/d + β ≥ 0; the coordinate projection onto k basis vectors gives (kd − 1)α + d(k − 1)β ≤ kd; and the Fourier projection AA*, with A the first k columns of the normalized d × d discrete Fourier matrix, has rank k and every diagonal entry k/d, so it gives (kd − 1)α + k(d − 1)β ≤ kd for every k ≤ d. Conversely the k-positive parameters form a convex set containing the four vertices, where Q ≥ 0 follows from Cauchy–Schwarz on the diagonal and from |tr(U*W)|² ≤ k‖U*W‖².

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.KPositive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.fourierRows`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.fourierRows_gram`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.phi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.quadrilateral`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
