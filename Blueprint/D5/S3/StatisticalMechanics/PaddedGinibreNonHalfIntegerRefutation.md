# A non-half-integer exponent violates the PGG inequalities

## Abstract

The padded general Ginibre inequalities for stable determinantal polynomials fail at exponent 1/4. Three positive semidefinite real matrices of size two, a positive definite sum, trivial parity and four rows give a strictly negative PGG sum.

**Definition 1.1 (Determinantal polynomial).**

$$\forall n : \mathbb{N}, \forall q : \mathbb{N}, \forall A : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(q\right), \operatorname{Fin}\left(q\right), \mathbb{R}\right), \forall x : \operatorname{Fin}\left(n\right) \to \mathbb{R}, \operatorname{P}\left(A, x\right) = \operatorname{det}\left(\sum_{j:\operatorname{Fin}\left(n\right)} \operatorname{smul}\left(x\left(j\right), A\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.P` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 9: "Let q ∈ ℕ_{>0}, and let A₁, …, Aₙ be n real symmetric positive semidefinite matrices of q × q format. Suppose that A₁ + ⋯ + Aₙ is positive definite and define the polynomial P(x) = det(x₁A₁ + ⋯ xₙAₙ) which is then strictly positive for x ∈ (0, ∞)ⁿ." Here A is an explicit argument, its indices run over Fin(n), x has real coordinates, and each A_j is a Matrix(Fin(q), Fin(q), R).

**Definition 1.2 (Even multi-indices).**

$$\forall n : \mathbb{N}, \forall L : \mathbb{N}, \forall \rho : (\operatorname{Fin}\left(n\right) \to \mathbb{Z}) \to+ (\operatorname{Fin}\left(L\right) \to \operatorname{ZMod}\left(2\right)), \forall a : \operatorname{Fin}\left(n\right) \to \mathbb{N}, (\operatorname{evenIndex}\left(\rho, a\right)) \Leftrightarrow (\rho\left(j\mapsto\operatorname{castInt}\left(a\left(j\right)\right)\right) = 0)$$

*Formalization.* `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.evenIndex` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 5: "Suppose we are given a group homomorphism ρ : ℤⁿ → (ℤ/2ℤ)ᴸ, for some integer L ≥ 0." "We will say that a is even iff ρ(a) = 0." The carrier is the additive homomorphism (Fin(n) -> Z) ->+ (Fin(L) -> ZMod(2)); castInt casts each natural coordinate of a to an integer. L = 0 is allowed.

**Definition 1.3 (The padded general Ginibre sum).**

$$\forall n : \mathbb{N}, \forall q : \mathbb{N}, \forall L : \mathbb{N}, \forall m : \mathbb{N}, \forall A : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(q\right), \operatorname{Fin}\left(q\right), \mathbb{R}\right), \forall \rho : (\operatorname{Fin}\left(n\right) \to \mathbb{Z}) \to+ (\operatorname{Fin}\left(L\right) \to \operatorname{ZMod}\left(2\right)), \forall V : \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall \varepsilon : \operatorname{Fin}\left(m\right) \to \mathbb{Z}, \forall u : \operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall eta : \mathbb{R}, \operatorname{pggSum}\left(A, \rho, V, \varepsilon, u, eta\right) = \sum_{\alpha:\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right)} (\operatorname{indicator}\left(\operatorname{evenIndex}\left(\rho, \operatorname{vecMul}\left(i\mapsto\operatorname{val}\left(\alpha\left(i\right)\right), V\right)\right)\right) \cdot (\prod_{i:\operatorname{Fin}\left(m\right)} \operatorname{castReal}\left(\varepsilon\left(i\right)\right)^{1 - \operatorname{val}\left(\alpha\left(i\right)\right)}) \cdot \operatorname{P}\left(A, j\mapsto\operatorname{castReal}\left(u\left(j\right) + \operatorname{vecMul}\left(i\mapsto\operatorname{val}\left(\alpha\left(i\right)\right), V\right)\left(j\right)\right)\right)^{-eta} \cdot \operatorname{P}\left(A, j\mapsto\operatorname{castReal}\left(u\left(j\right) + \operatorname{vecMul}\left(i\mapsto1 - \operatorname{val}\left(\alpha\left(i\right)\right), V\right)\left(j\right)\right)\right)^{-eta})$$

*Formalization.* `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.pggSum` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

The sum in Theorem 2.3 (p. 10) uses pairs of natural vectors alpha + beta = 1_m and the sign epsilon^beta = product_i epsilon_i^{beta_i} (p. 6). Here alpha : Fin(m) -> Fin(2) indexes each pair once, val(alpha_i) is its natural value, and beta_i = 1 - val(alpha_i); this subtraction is in N and has no truncation because val(alpha_i) is 0 or 1. Vector-matrix multiplication vecMul(a,V) is Mathlib Matrix.vecMul: its j-th coordinate is the sum of a_i V_ij. The indicator is 1 for an even alpha V and 0 otherwise. castReal casts the natural padded coordinates and integer signs to R, and all powers with exponent -eta are Real.rpow.

**Definition 1.4 (Problem 3: arbitrary positive real exponents).**

$$(claim) \Leftrightarrow (\forall eta : \mathbb{R}, (0 < eta) \Rightarrow (\forall n : \mathbb{N}, \forall q : \mathbb{N}, \forall L : \mathbb{N}, \forall A : \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(q\right), \operatorname{Fin}\left(q\right), \mathbb{R}\right), \forall \rho : (\operatorname{Fin}\left(n\right) \to \mathbb{Z}) \to+ (\operatorname{Fin}\left(L\right) \to \operatorname{ZMod}\left(2\right)), (0 < q) \Rightarrow ((\forall j : \operatorname{Fin}\left(n\right), \operatorname{PosSemidef}\left(A\left(j\right)\right)) \Rightarrow ((\operatorname{PosDef}\left(\sum_{j:\operatorname{Fin}\left(n\right)} A\left(j\right)\right)) \Rightarrow (\forall m : \mathbb{N}, \forall V : \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall \varepsilon : \operatorname{Fin}\left(m\right) \to \mathbb{Z}, \forall u : \operatorname{Fin}\left(n\right) \to \mathbb{N}, (\operatorname{evenIndex}\left(\rho, \operatorname{vecMul}\left(\operatorname{const}\left(\operatorname{Fin}\left(m\right), 1\right), V\right)\right)) \Rightarrow ((\forall i : \operatorname{Fin}\left(m\right), (\varepsilon\left(i\right) = 1) \lor (\varepsilon\left(i\right) = -1)) \Rightarrow ((\forall j : \operatorname{Fin}\left(n\right), 0 < u\left(j\right)) \Rightarrow ((\operatorname{evenIndex}\left(\rho, u\right)) \Rightarrow (0 \le \operatorname{pggSum}\left(A, \rho, V, \varepsilon, u, eta\right))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.claim` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 14: "Problem 3: In the light of investigations of spin models with non-integer number of components N, as in [8], it would be interesting to see if Thm. 2.3 still holds for P^{−η} where η is any positive real number instead of being restricted to half integers." The displayed claim keeps every quantifier and hypothesis of Theorem 2.3 (p. 10): eta > 0, n, q and L in N, q > 0, every A_j positive semidefinite, their sum positive definite, every m, natural V, integer signs in {-1,1}, positive natural u, and even 1_m V and u. Here const(Fin(m),1) denotes Mathlib Function.const (Fin m) (1 : ℕ). For real matrices PosSemidef includes symmetry, and PosDef includes strict positivity on every nonzero vector. Fin indices are zero-based; no condition n > 0 or m > 0 is added. The binary convention for the sum is stated above.

**Theorem 1.5 (The extension to every positive exponent is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Take eta = 1/4, n = 3, q = 2, L = 0, m = 4, the zero parity map, u = (1,1,1), every epsilon_i = -1, and rows V = (1,0,0), (1,0,0), (0,1,0), (0,0,1). The matrices are [[1,0],[0,0]], [[0,0],[0,1]], [[1,1],[1,1]]. Their quadratic forms are v_0^2, v_1^2, (v_0+v_1)^2; the sum has form v_0^2 + v_1^2 + (v_0+v_1)^2 and is positive definite. The determinant is x_0 x_1 + x_0 x_2 + x_1 x_2. The sixteen terms combine into Theta = 2*48^(-1/4) - 4*55^(-1/4) + 2*56^(-1/4) - 4*60^(-1/4) + 4*64^(-1/4). Integer fourth-power comparisons give 48*3800^4, 56*3656^4, 64*3536^4 > 10^16 and 55*3672^4, 60*3593^4 < 10^16. Monotonicity of the fourth power gives upper bounds for the three powers with positive coefficients and lower bounds for the two powers with negative coefficients, so Theta < (2*3800 - 4*3672 + 2*3656 - 4*3593 + 4*3536)/10000 = -1/2500 < 0.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.P`
- Truth anchor: `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.evenIndex`
- Truth anchor: `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.pggSum`
- Truth anchor: `D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.result`
