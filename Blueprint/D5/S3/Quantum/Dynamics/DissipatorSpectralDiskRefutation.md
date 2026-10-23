# The pure-state scale does not confine dissipative spectra

## Abstract

A traceless diagonal jump on three complex coordinates gives an eigenvalue outside the disk determined by the pure-state scale.

**Definition 1.1 (The dissipator of one jump).**

$$\forall \left(N: \mathbb{N}\right), \left(\forall \left(L: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)\right), \left(\operatorname{dissipator}\left(L, \rho\right) = L \cdot \rho \cdot \operatorname{Matrix.conjTranspose}\left(L\right) - \left(\frac{1}{2}: \mathbb{C}\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(L\right) \cdot L \cdot \rho + \rho \cdot \left(\operatorname{Matrix.conjTranspose}\left(L\right) \cdot L\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.dissipator` (`✓ std3`).

*Citation.* Dariusz Chruściński; Sergey Denisov; Wojciech Tarnowski; Karol Życzkowski (2025). *Spectral delineation of Markov generators: classical vs quantum*. DOI: [10.1088/1751-8121/ae58d2](https://doi.org/10.1088/1751-8121/ae58d2). URL: <https://arxiv.org/abs/2504.07903v1>.

*Commentary.*

For a complex square matrix L, the dissipator sends ρ to LρLᴴ minus one half of the sum LᴴLρ + ρLᴴL. Here Lᴴ is the conjugate transpose. This is one summand of the GKLS expression in bounding_6.tex, lines 205–209. There is no Hamiltonian commutator. The definition permits every natural N and every pair of matrices L and ρ, without a positivity or trace assumption.

**Definition 1.2 (A finite sum of dissipators).**

$$\forall \left(N: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(\gamma: \operatorname{Fin}\left(m\right) \to \mathbb{R}\right), \left(\forall \left(L: \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)\right), \left(\operatorname{generator}\left(\gamma, L, \rho\right) = \sum_{k: \operatorname{Fin}\left(m\right)} \left(\operatorname{Complex.ofReal}\left(\gamma\left(k\right)\right) \cdot \operatorname{dissipator}\left(L\left(k\right), \rho\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.generator` (`✓ std3`).

*Citation.* Dariusz Chruściński; Sergey Denisov; Wojciech Tarnowski; Karol Życzkowski (2025). *Spectral delineation of Markov generators: classical vs quantum*. DOI: [10.1088/1751-8121/ae58d2](https://doi.org/10.1088/1751-8121/ae58d2). URL: <https://arxiv.org/abs/2504.07903v1>.

*Commentary.*

The generator is the sum of the dissipators of L(k), weighted by the real rates γ(k). Each rate is explicitly included in the complex scalars by Complex.ofReal. A dot between a complex scalar and a matrix denotes scalar multiplication; between two matrices it denotes matrix multiplication. The expression is the purely dissipative part of the source's GKLS formula, bounding_6.tex, lines 205–209 and 227; line 702 fixes the purely dissipative scope. The definition itself allows arbitrary real rates, with nonnegativity imposed in claim.

**Definition 1.3 (The supremum over unit vectors).**

$$\forall \left(N: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(\gamma: \operatorname{Fin}\left(m\right) \to \mathbb{R}\right), \left(\forall \left(L: \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)\right), \left(\operatorname{scale}\left(\gamma, L\right) = \operatorname{sSup}\left(\{r: \mathbb{R} \mid \exists \left(\psi: \operatorname{Fin}\left(N\right) \to \mathbb{C}\right), \left(\left(\sum_{i: \operatorname{Fin}\left(N\right)} \left(\left\lVert \psi\left(i\right) \right\rVert^{2}\right) = \left(1: \mathbb{R}\right)\right) \land \left(r = \left\lVert \operatorname{dotProduct}\left(\operatorname{star}\left(\psi\right), \operatorname{Matrix.mulVec}\left(\operatorname{generator}\left(\gamma, L, \operatorname{Matrix.vecMulVec}\left(\psi, \operatorname{star}\left(\psi\right)\right)\right), \psi\right)\right) \right\rVert\right)\right)\}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.scale` (`✓ std3`).

*Citation.* Dariusz Chruściński; Sergey Denisov; Wojciech Tarnowski; Karol Życzkowski (2025). *Spectral delineation of Markov generators: classical vs quantum*. DOI: [10.1088/1751-8121/ae58d2](https://doi.org/10.1088/1751-8121/ae58d2). URL: <https://arxiv.org/abs/2504.07903v1>.

*Commentary.*

For every vector ψ with sum of squared coordinate norms equal to one, form the rank-one matrix ψψᴴ, apply the generator, and evaluate its quadratic form at ψ. The scale is the real supremum of the norms of these complex values. The star on a vector conjugates each coordinate; Matrix.vecMulVec forms the outer product, Matrix.mulVec is matrix-vector multiplication, and dotProduct is the bilinear dot product, so its first argument is explicitly conjugated. This is the supremum form of the pure-state maximum in Conjecture 3, bounding_6.tex, lines 1044–1049. No maximizing vector or positive scale is assumed in this definition.

**Definition 1.4 (The proposed disk bound).**

$$\operatorname{claim} = \left(\forall \left(N: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(\gamma: \operatorname{Fin}\left(m\right) \to \mathbb{R}\right), \left(\forall \left(L: \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)\right), \left(\left(\forall \left(k: \operatorname{Fin}\left(m\right)\right), \left(\left(0: \mathbb{R}\right) \le \gamma\left(k\right)\right)\right) \Rightarrow \left(\left(\forall \left(k: \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Matrix.trace}\left(L\left(k\right)\right) = \left(0: \mathbb{C}\right)\right)\right) \Rightarrow \left(\left(\left(0: \mathbb{R}\right) < \operatorname{scale}\left(\gamma, L\right)\right) \Rightarrow \left(\forall \left(lam: \mathbb{C}\right), \left(\forall \left(X: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)\right), \left(\left(X \ne \left(0: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)\right)\right) \Rightarrow \left(\left(\operatorname{generator}\left(\gamma, L, X\right) = lam \cdot X\right) \Rightarrow \left(\left\lVert \left(1: \mathbb{C}\right) + \frac{lam}{\operatorname{Complex.ofReal}\left(\operatorname{scale}\left(\gamma, L\right)\right)} \right\rVert \le \left(1: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.claim` (`✓ std3`).

*Citation.* Dariusz Chruściński; Sergey Denisov; Wojciech Tarnowski; Karol Życzkowski (2025). *Spectral delineation of Markov generators: classical vs quantum*. DOI: [10.1088/1751-8121/ae58d2](https://doi.org/10.1088/1751-8121/ae58d2). URL: <https://arxiv.org/abs/2504.07903v1>.

*Commentary.*

For every natural N and m, every family of nonnegative real rates and traceless complex jump matrices with strictly positive scale would satisfy the stated bound for every complex eigenvalue lam and nonzero eigenmatrix X. The bound says that lam divided by the scale lies in the closed disk of radius one centred at minus one. Complex.ofReal explicitly includes the real scale in the complex denominator. This is the spectral assertion of Conjecture 3, bounding_6.tex, lines 1044–1050, for finite purely dissipative GKLS sums. The traceless condition appears in the canonical form at lines 794–799. No orthogonality or normalization of the jump matrices is assumed here; zero rates are allowed and contribute zero summands.

**Theorem 1.5 (A three-dimensional counterexample).**

$$\neg \left(\operatorname{claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/chruscinski-denisov-tarnowski-zyczkowski-2025-dissipator-spectral-disk-refutation` (refuted) by `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chruscinski-denisov-tarnowski-zyczkowski-2025-dissipator-spectral-disk-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dariusz Chruściński; Sergey Denisov; Wojciech Tarnowski; Karol Życzkowski (2025). *Spectral delineation of Markov generators: classical vs quantum*. DOI: [10.1088/1751-8121/ae58d2](https://doi.org/10.1088/1751-8121/ae58d2). URL: <https://arxiv.org/abs/2504.07903v1>.

*Commentary.*

Take N = 3 and m = 1, put γ(k) = 1, and let L(k) be the diagonal matrix V = diag(1 − i/3, −1 − i/3, 2i/3). Its trace is zero: the two real parts cancel and the three imaginary parts sum to zero.

For an arbitrary ψ in Fin 3 → ℂ, put p₀ = ‖ψ 0‖², p₁ = ‖ψ 1‖², and p₂ = ‖ψ 2‖². Expanding the diagonal products gives ψᴴ generator(γ,L,ψψᴴ) ψ = Complex.ofReal((p₀ − p₁)² + p₂² − (p₀ + p₁ + p₂)²). This identity holds before imposing normalization.

If the squared coordinate norms of ψ sum to one, then p₀ + p₁ + p₂ = 1. All three p values are nonnegative. Set q = 1 − (p₀ − p₁)² − p₂². The identity q = 4p₀p₁ + 2p₂(p₀ + p₁) gives q ≥ 0, and the squared terms in its defining expression give q ≤ 1. The quadratic form is therefore Complex.ofReal(−q), whose norm is q ≤ 1. The set defining the scale is nonempty: ψ = (1,0,0) gives value zero. Taking its supremum proves scale(γ,L) ≤ 1.

Next choose ψ = ((1+i)/2,(1+i)/2,0). Since ‖1+i‖² = 2, its squared coordinate norms sum to one and p₀ = p₁ = 1/2, p₂ = 0. The same quadratic-form identity gives norm one. The preceding bound makes the set of values bounded above, so membership of the value one implies 1 ≤ scale(γ,L), and in particular scale(γ,L) > 0.

Let X be the matrix with entry one at row 0, column 1 and zero elsewhere. Expanding the nine entries gives generator(γ,L,X) = (−2 + (2/3)i)X. Thus lam = −2 + (2/3)i is an eigenvalue.

For any real ν with 0 < ν ≤ 1, the squared norm of 1 + (−2 + (2/3)i)/Complex.ofReal(ν) is (1 − 2/ν)² + (2/(3ν))². Its difference from one is (40/9 − 4ν)/ν² > 0. Nonnegativity of the norm then gives a norm strictly greater than one.

Suppose claim held. Apply it to N = 3, m = 1 and the family above: the rate is nonnegative, every jump has trace zero, and the scale is positive. The matrix X is nonzero because its (0,1) entry is one. Its eigenvalue equation would give a disk norm at most one. Applying the strict inequality with ν = scale(γ,L), using its positivity and upper bound by one, contradicts that conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.dissipator`
- Truth anchor: `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.generator`
- Truth anchor: `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.scale`
