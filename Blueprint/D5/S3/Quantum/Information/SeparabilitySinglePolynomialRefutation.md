# No single polynomial inequality characterizes bipartite separability

## Abstract

An affine family of qubit–qutrit density operators excludes a single polynomial inequality characterizing separability, even when the polynomial may depend on the local dimensions.

**Definition 1.1 (Real and imaginary matrix coordinates).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right)), (\forall (p: (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right))), (\forall (q: (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right))), (\forall (b: \operatorname{Bool}), (\operatorname{coords}\left(\rho\right)\left((p, (q, b))\right) = \operatorname{ite}\left(b = \operatorname{true}, \operatorname{Complex.im}\left(\rho\left(p, q\right)\right), \operatorname{Complex.re}\left(\rho\left(p, q\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.coords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* O. Krüger; R. F. Werner (2005). *Some Open Problems in Quantum Information Theory*. URL: <https://arxiv.org/abs/quant-ph/0504166v1>.

*Commentary.*

For a bipartite complex matrix, the coordinate indexed by (p,q,b) is the imaginary part of the entry at (p,q) when b is true, and its real part otherwise. The index type is (Fin m × Fin n) × ((Fin m × Fin n) × Bool). This concrete coordinate encoding expresses real polynomials in matrix entries; it imposes no positivity or normalization condition.

**Definition 1.2 (Polynomial invariance on density operators).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (f: \operatorname{MvPolynomial}\left(((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \times ((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \times \operatorname{Bool})), \mathbb{R}\right)), ((\operatorname{IsInvariant}\left(f\right)) \Leftrightarrow (\forall (UA: \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(m\right), \mathbb{C}\right)), (\forall (UB: \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right)), ((\operatorname{IsDensity}\left(\rho\right)) \to (\operatorname{MvPolynomial.eval}\left(\operatorname{coords}\left(((\operatorname{Matrix.kronecker}\left((\operatorname{Subtype.val}\left(UA\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)), (\operatorname{Subtype.val}\left(UB\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))\right)) \cdot (\rho)) \cdot (\operatorname{Matrix.conjTranspose}\left(\operatorname{Matrix.kronecker}\left((\operatorname{Subtype.val}\left(UA\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)), (\operatorname{Subtype.val}\left(UB\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right))\right)\right))\right), f\right) = \operatorname{MvPolynomial.eval}\left(\operatorname{coords}\left(\rho\right), f\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.IsInvariant` (`✓ std3`).

*Citation.* O. Krüger; R. F. Werner (2005). *Some Open Problems in Quantum Information Theory*. URL: <https://arxiv.org/abs/quant-ph/0504166v1>.

*Commentary.*

Krüger–Werner, Problem 3, defines equally entangled states by conjugation with arbitrary local unitaries, and an entanglement invariant as a real function constant on these orbits. A polynomial invariant is polynomial in the matrix entries. Real and imaginary coordinates express such a function as a real multivariate polynomial. Density operators are positive semidefinite matrices with trace one:

$$
\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right)), ((\operatorname{IsDensity}\left(\rho\right)) \Leftrightarrow ((\operatorname{Matrix.PosSemidef}\left(\rho\right)) \land (\operatorname{Matrix.trace}\left(\rho\right) = 1)))))
$$

The displayed invariance condition is required only on density operators. Each local unitary is explicitly coerced to its complex matrix before taking the tensor product, and the final factor is the conjugate transpose of that tensor product.

**Definition 1.3 (The single-inequality separability question).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), ((2 \le m) \to ((2 \le n) \to (\exists (f: \operatorname{MvPolynomial}\left(((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \times ((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \times \operatorname{Bool})), \mathbb{R}\right)), ((\operatorname{IsInvariant}\left(f\right)) \land (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right)), ((\operatorname{IsDensity}\left(\rho\right)) \to ((0 \le \operatorname{MvPolynomial.eval}\left(\operatorname{coords}\left(\rho\right), f\right)) \Leftrightarrow (\operatorname{separableCone}\left(\rho\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.claim` (`✓ std3`).

*Citation.* O. Krüger; R. F. Werner (2005). *Some Open Problems in Quantum Information Theory*. URL: <https://arxiv.org/abs/quant-ph/0504166v1>.

*Commentary.*

The third closely related problem in Problem 3 asks for a polynomial invariant f such that f(ρ) ≥ 0 is equivalent to separability, allowing f to depend on the dimensions. Here m and n range over all natural local dimensions at least two. For each pair of dimensions one polynomial must classify every density operator. The predicate separableCone means a finite sum of tensor products of positive semidefinite matrices; at trace one this is precisely a separable state. No degree bound is imposed. The source's solution using separation of compact-group orbits answers the main completeness question for polynomial invariants; it does not answer this single-inequality subquestion.

**Theorem 1.4 (An affine qubit–qutrit family gives a contradiction).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kruger-werner-2005-single-polynomial-separability-refutation` (refuted) by `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kruger-werner-2005-single-polynomial-separability-refutation","declaration_gid":"D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* O. Krüger; R. F. Werner (2005). *Some Open Problems in Quantum Information Theory*. URL: <https://arxiv.org/abs/quant-ph/0504166v1>.

*Commentary.*

Take local dimensions m = 2 and n = 3. In the ordered basis e₀ = |00⟩, e₁ = |01⟩, e₂ = |02⟩, e₃ = |10⟩, e₄ = |11⟩, e₅ = |12⟩, define the real symmetric matrix ρ(x,y) by the diagonal (a,b,c,c,a,b), where a = (5 + 3x − y)/40, b = (5 − x + 3y)/40 and c = (5 − x − y)/20. Its only nonzero off-diagonal entries are ρ₁₃ = ρ₃₁ = (−5 + 5x + y)/40 and ρ₂₄ = ρ₄₂ = (−5 + x + 5y)/40. All these real entries are embedded in ℂ. The trace is one, and the family is affine: writing B₀ = ρ(0,0), B₁ = ρ(1,0) and B₂ = ρ(0,1), one has ρ(x,y) = (1 − x − y)B₀ + xB₁ + yB₂.

For a complex vector v write P(v) = vvᴴ, without normalizing v. The identity ρ(x,y) = Σⱼ cⱼ P(vⱼ) has the eight vectors (e₀, e₅, 2e₁ − 3e₃, 2e₄ − 3e₂, e₁, e₄, e₃, e₂) and the corresponding real coefficients ((5 + 3x − y)/40, (5 − x + 3y)/40, (5 − 5x − y)/240, (5 − x − 5y)/240, (5 + 7x + 11y)/120, (5 + 11x + 7y)/120, (5 + 11x − y)/80, (5 − x + 11y)/80). Each coefficient is nonnegative when |x|,|y| ≤ 1/4. Thus every matrix in this square is a density operator.

The three corner states have explicit product decompositions. Each is a sum Σⱼ cⱼ P(aⱼ) ⊗ P(bⱼ). For B₀, the pairs (aⱼ,bⱼ) are ((1,1),(1,−1,1)), ((1,i),(−1,i,1)), ((1,−1),(1,1,1)), ((1,−i),(−1,−i,1)), ((1,0),(0,0,1)) and ((0,1),(1,0,0)); the coefficients are (1/32,1/32,1/32,1/32,1/8,1/8). For both B₁ and B₂ the first-factor vectors are ((1,1),(1,i),(1,−1),(1,−i),(1,0),(0,1),(1,0),(0,1)), and the coefficients are (1/40,1/40,1/40,1/40,1/10,1/10,1/5,1/5). For B₁ the second-factor vectors are ((0,1,−1),(0,1,−i),(0,1,1),(0,1,i),(0,0,1),(0,1,0),(1,0,0),(1,0,0)); for B₂ they are ((1,−1,0),(1,−i,0),(1,1,0),(1,i,0),(0,1,0),(1,0,0),(0,0,1),(0,0,1)). Here i is the imaginary unit, and all vectors are unnormalized. These sums are separable and have trace one. If 0 ≤ x,y ≤ 1/4, the affine coefficients 1 − x − y, x and y are nonnegative, so ρ(x,y) is separable.

Let Γ transpose the qutrit factor. The real quadratic forms of Γ(ρ(x,y)) on e₀ + e₄ and e₁ + e₅ are 2x/5 and 2y/5, respectively. Every separable matrix has positive semidefinite partial transpose. Hence ρ(x,y) is entangled whenever x < 0 or y < 0 and |x|,|y| ≤ 1/4.

Suppose a polynomial f satisfies the claimed equivalence at dimensions 2 and 3, and put q(x,y) = f(ρ(x,y)), meaning evaluation in the real and imaginary entry coordinates. Affineness makes q a polynomial. Fix 0 < y < 1/4. Separability at x = 0 gives q(0,y) ≥ 0, whereas entanglement for −1/4 < x < 0 gives q(x,y) < 0. Continuity as x tends to zero from below forces q(0,y) = 0. The univariate polynomial y ↦ q(0,y) therefore has infinitely many roots and is identically zero. In particular q(0,−1/8) = 0 ≥ 0, although ρ(0,−1/8) is a density operator with a negative partial-transpose quadratic form. This contradicts the proposed equivalence. The argument uses neither local-unitary invariance nor a degree bound. The affine family and all the decompositions above are constructions here.

## References

- Truth anchor: `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.IsInvariant`
- Truth anchor: `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.coords`
- Truth anchor: `D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity](../Entanglement/AbsolutePPT/QuadbitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](SLDSpectralEnergy.md)
