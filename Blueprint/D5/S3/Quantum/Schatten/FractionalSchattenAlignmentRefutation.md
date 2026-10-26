# Word traces do not control fractional Schatten norms

## Abstract

Domination of every word trace does not order Schatten norms of non-integer order.

**Definition 1.1 (The proposed implication for every real order at least one).**

$$\left(\operatorname{D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation.claim}: \operatorname{Prop}\right) = \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(a_{0}: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right), \left(\forall \left(a_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right), \left(\forall \left(b_{0}: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right), \left(\forall \left(b_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(a_{0}\right)\right) \to \left(\left(\operatorname{Matrix.PosSemidef}\left(a_{1}\right)\right) \to \left(\left(\operatorname{Matrix.PosSemidef}\left(b_{0}\right)\right) \to \left(\left(\operatorname{Matrix.PosSemidef}\left(b_{1}\right)\right) \to \left(\left(\operatorname{Matrix.charpoly}\left(a_{0}\right) = \operatorname{Matrix.charpoly}\left(b_{0}\right)\right) \to \left(\left(\operatorname{Matrix.charpoly}\left(a_{1}\right) = \operatorname{Matrix.charpoly}\left(b_{1}\right)\right) \to \left(\left(\forall \left(s: \operatorname{List}\left(\operatorname{Bool}\right)\right), \left(\left(\operatorname{Complex.im}\left(\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Observer.Hankel.WordHankelRealization.wordProduct}\left(\lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\operatorname{ite}\left(b = \operatorname{Bool.true}, a_{1}, a_{0}\right)\right), s\right)\right)\right) = \left(0: \mathbb{R}\right)\right) \land \left(\left\lVert \operatorname{Matrix.trace}\left(\operatorname{D5.S3.Observer.Hankel.WordHankelRealization.wordProduct}\left(\lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\operatorname{ite}\left(b = \operatorname{Bool.true}, b_{1}, b_{0}\right)\right), s\right)\right) \right\rVert \le \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Observer.Hankel.WordHankelRealization.wordProduct}\left(\lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\operatorname{ite}\left(b = \operatorname{Bool.true}, a_{1}, a_{0}\right)\right), s\right)\right)\right)\right)\right)\right) \to \left(\forall \left(p: \mathbb{R}\right), \left(\left(\left(1: \mathbb{R}\right) \le p\right) \to \left(\operatorname{schattenNorm}\left(b_{0} + b_{1}, p\right) \le \operatorname{schattenNorm}\left(a_{0} + a_{1}, p\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammad A. Alhejji; Emanuel Knill (2024). *Towards a Resolution of the Spin Alignment Problem*. DOI: [10.1007/s00220-024-04980-1](https://doi.org/10.1007/s00220-024-04980-1). URL: <https://arxiv.org/abs/2307.06894v3>.

*Commentary.*

Alhejji and Knill ask whether domination of the traces of all ordered products of two positive semidefinite matrices, with the individual spectra fixed, implies domination of the Schatten norms of their sums for every real p ≥ 1 (arXiv:2307.06894v3, main.tex, line 759). Their spectrum lists eigenvalues with multiplicity (line 117), and their Schatten norm is ‖R‖ₚ = (tr |R|ᵖ)^(1/p), with |R| = √(RᴴR), where Rᴴ is the adjoint (lines 274–278).

The assertion quantifies over every natural matrix size m, including zero, and four complex matrices a₀, a₁, b₀, b₁ of that size. Each matrix is positive semidefinite, and the characteristic polynomials agree for a₀ and b₀ and for a₁ and b₁. For these Hermitian matrices, the latter equalities express equality of spectra with multiplicity. A Boolean word s selects the subscript one at true and zero at false; its ordered product is taken from left to right, and the empty product is the identity. For every word, the a-trace has imaginary part zero and its real part is at least the complex norm of the b-trace. The conclusion compares the Schatten norms of b₀ + b₁ and a₀ + a₁ at every real p ≥ 1.

**Theorem 1.2 (A diagonal counterexample at order three halves).**

$$\neg \left(\operatorname{D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/alhejji-knill-2024-fractional-schatten-alignment` (refuted) by `D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alhejji-knill-2024-fractional-schatten-alignment","declaration_gid":"D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohammad A. Alhejji; Emanuel Knill (2024). *Towards a Resolution of the Spin Alignment Problem*. DOI: [10.1007/s00220-024-04980-1](https://doi.org/10.1007/s00220-024-04980-1). URL: <https://arxiv.org/abs/2307.06894v3>.

*Commentary.*

Take A₀ = B₀ = diag(0, 1, 1, 2), A₁ = diag(1, 0, 1, 2), and B₁ = diag(0, 1, 2, 1), as complex matrices of size four. For diagonal matrices with diagonals d₀ and d₁, induction on a Boolean word s shows that its ordered product is diagonal with kth entry d₀(k)^m d₁(k)^n, where m counts false and n counts true. The empty word gives the identity, and adjoining either letter multiplies the corresponding diagonal entry and increments its count.

Taking traces gives tr Πs(A₀,A₁) = ↑(0^m + 0^n + 1 + 2^(m+n)) and tr Πs(B₀,B₁) = ↑(0^(m+n) + 1 + 2^m + 2^n), where each expression inside ↑ is a natural number, included in ℂ, and 0^0 = 1. If either count is zero the two natural numbers agree. If both counts are positive, 2 ≤ 2^m and 2 ≤ 2^n imply 2^m + 2^n ≤ 2^m · 2^n = 2^(m+n); adding one gives the required comparison because all three relevant positive powers of zero vanish.

All diagonal entries are nonnegative, so the four matrices are positive semidefinite. The equality A₀ = B₀ gives one characteristic-polynomial equality. Expanding the diagonal characteristic polynomials for A₁ and B₁ gives the same product of the four linear factors in a different order, so the other equality also holds. The trace formulas are complex inclusions of natural numbers, hence have imaginary part zero; the norm and real part of each inclusion are that natural number cast to ℝ. The natural-number comparison therefore proves the required word-trace inequalities.

For a real nonnegative diagonal d and a real p ≥ 1, the Schatten norm of diag(k ↦ (d(k) : ℂ)) is (Σk d(k)^p)^(1/p). To obtain this identity, write D = diag(k ↦ (d(k) : ℂ)). Then Dᴴ · (Dᴴ)ᴴ = DᴴD is diag(k ↦ ((d(k)^2 : ℝ) : ℂ)). Continuous functional calculus acts entry by entry on this diagonal matrix. Taking the trace and then its real part reduces the expression to a sum, and nonnegativity gives (d(k)^2)^(p/2) = d(k)^p.

The sums A₀ + A₁ and B₀ + B₁ have diagonals (1, 1, 2, 4) and (0, 2, 3, 3), respectively. Their entries are nonnegative. At p = 3/2, the diagonal norm identity and strict monotonicity of the real power x ↦ x^(2/3) on nonnegative x reduce the strict norm comparison to 1^(3/2) + 1^(3/2) + 2^(3/2) + 4^(3/2) < 0^(3/2) + 2^(3/2) + 3^(3/2) + 3^(3/2). Here 4^(3/2) = 8 and 3^(3/2) = 3√3. After cancellation the inequality is 10 < 6√3, which follows from (√3)^2 = 3 and √3 ≥ 0 since 100 < 108. Thus ‖A₀ + A₁‖₃⁄₂ < ‖B₀ + B₁‖₃⁄₂.

If the asserted implication held, its instance at size four, these matrices and p = 3/2 would give the opposite weak inequality. The strict comparison contradicts it. This disproves the implication from all word traces to all real orders p ≥ 1; it does not decide the spin alignment conjecture itself.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.result`
- Dependency: [D5/S3/Observer/Hankel/WordHankelRealization](../../Observer/Hankel/WordHankelRealization.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Schatten/Holder](Holder.md)
