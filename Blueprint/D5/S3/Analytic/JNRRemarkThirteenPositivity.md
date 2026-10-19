# A sum of squares for the JNR triple sum

## Abstract

The JNR triple sum is positive for every configuration of distinct poles with positive weights.

Cork and Disney-Hogg's expression (18) has two outer sums that can be combined into inner products of weighted vector sums. Completing a square at a weighted barycentre proves positivity without the balance condition (15). All sums below range over Fin (N + 1), so each ordered triple, including repeated indices, is counted once.

**Definition 1.1 (The zero-parameter density).**

$$\forall (N : \mathbb{N}), \forall (lam : \operatorname{Fin}\left((N + 1)\right) \to \mathbb{R}), \forall (y : \operatorname{Fin}\left((N + 1)\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, (\operatorname{Fin}\left(3\right))\right)), \operatorname{rho0}\left(lam, y\right) = \sum_{i : \operatorname{Fin}\left((N + 1)\right)} \frac{\operatorname{lam}\left(i\right)^{2}}{\left\lVert \operatorname{y}\left(i\right) \right\rVert^{2}}$$

*Formalization.* `D5/S3/Analytic/JNRRemarkThirteenPositivity.rho0` (`✓ std3`).

*Citation.* Josh Cork and Linden Disney-Hogg (2025). *Locations of JNR skyrmions*. DOI: [10.1007/s11040-025-09513-3](https://doi.org/10.1007/s11040-025-09513-3). URL: <https://arxiv.org/abs/2505.00075v2>.

*Commentary.*

Equation (3), PDF page 4 (printed page 3), defines “ρ(μ) = Σ_{i=0}^N λᵢ² / |x − aᵢ + μ|²”. At μ = 0, with yᵢ = aᵢ − x and the Euclidean norm of pure imaginary quaternions, this is the displayed density. The weights are the real function lam and the vectors form the function y; the definition uses total real division.

**Definition 1.2 (The triple sum in expression (18)).**

$$\forall (N : \mathbb{N}), \forall (lam : \operatorname{Fin}\left((N + 1)\right) \to \mathbb{R}), \forall (mu : \mathbb{R}), \forall (y : \operatorname{Fin}\left((N + 1)\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, (\operatorname{Fin}\left(3\right))\right)), \operatorname{S}\left(lam, mu, y\right) = \frac{1}{\operatorname{rho0}\left(lam, y\right)} \cdot (\sum_{i : \operatorname{Fin}\left((N + 1)\right)} \sum_{j : \operatorname{Fin}\left((N + 1)\right)} \sum_{k : \operatorname{Fin}\left((N + 1)\right)} \frac{\operatorname{lam}\left(i\right)^{2} \cdot \operatorname{lam}\left(j\right)^{2} \cdot \operatorname{lam}\left(k\right)^{2} \cdot \operatorname{inner}\left(\mathbb{R}, (\operatorname{y}\left(j\right) - \operatorname{y}\left(i\right)), (\operatorname{y}\left(j\right) - \operatorname{y}\left(k\right))\right)}{(\left\lVert \operatorname{y}\left(i\right) \right\rVert^{2} + mu^{2}) \cdot (\left\lVert \operatorname{y}\left(j\right) \right\rVert^{2} + mu^{2}) \cdot \left\lVert \operatorname{y}\left(j\right) \right\rVert^{2} \cdot \left\lVert \operatorname{y}\left(k\right) \right\rVert^{2}})$$

*Formalization.* `D5/S3/Analytic/JNRRemarkThirteenPositivity.S` (`✓ std3`).

*Citation.* Josh Cork and Linden Disney-Hogg (2025). *Locations of JNR skyrmions*. DOI: [10.1007/s11040-025-09513-3](https://doi.org/10.1007/s11040-025-09513-3). URL: <https://arxiv.org/abs/2505.00075v2>.

*Commentary.*

Appendix A, Remark 13, PDF page 20 (printed page 19): “As a consequence of (15), we can write” expression (18), followed by “where ρ(μ) is given in (3), and yᵢ = aᵢ − x_∗.” The displayed definition is that expression, with real inner product inner ℝ, lam for λ and mu for μ. Its value is defined for all inputs by total real division; positivity requires the hypotheses below.

**Definition 1.3 (The positivity conjecture).**

$$claim = (\forall (N : \mathbb{N}), (1 \le N) \Rightarrow (\forall (lam : \operatorname{Fin}\left((N + 1)\right) \to \mathbb{R}), \forall (mu : \mathbb{R}), \forall (a : \operatorname{Fin}\left((N + 1)\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, (\operatorname{Fin}\left(3\right))\right)), \forall (x : \operatorname{EuclideanSpace}\left(\mathbb{R}, (\operatorname{Fin}\left(3\right))\right)), (\forall (i : \operatorname{Fin}\left((N + 1)\right)), 0 < \operatorname{lam}\left(i\right)) \Rightarrow ((0 < mu) \Rightarrow ((\operatorname{Function.Injective}\left(a\right)) \Rightarrow ((\forall (i : \operatorname{Fin}\left((N + 1)\right)), x \ne \operatorname{a}\left(i\right)) \Rightarrow (0 < \operatorname{S}\left(lam, mu, (\lambda i \mapsto \operatorname{a}\left(i\right) - x)\right)))))))$$

*Formalization.* `D5/S3/Analytic/JNRRemarkThirteenPositivity.claim` (`✓ std3`).

*Citation.* Josh Cork and Linden Disney-Hogg (2025). *Locations of JNR skyrmions*. DOI: [10.1007/s11040-025-09513-3](https://doi.org/10.1007/s11040-025-09513-3). URL: <https://arxiv.org/abs/2505.00075v2>.

*Commentary.*

Appendix A, Remark 13, PDF page 20 (printed page 19): “The above proof shows that this is positive so long as Σᵢ (λᵢ²/|yᵢ|²) yᵢ = 0, however we conjecture that the sum in (18) is positive for any choice of yᵢ ∈ ℝ³∖{aᵢ}.” The index type Fin (N + 1) represents the N + 1 poles and 1 ≤ N ensures at least two of them. The poles a are injective, lam is positive at each pole, mu is positive, and x differs from every a i. The source's exclusion is read as x ≠ a i, hence a i − x ≠ 0. No balance equation is assumed.

**Theorem 1.4 (Strict positivity for every configuration).**

$$\forall (N : \mathbb{N}), (1 \le N) \Rightarrow (\forall (lam : \operatorname{Fin}\left((N + 1)\right) \to \mathbb{R}), \forall (mu : \mathbb{R}), \forall (a : \operatorname{Fin}\left((N + 1)\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, (\operatorname{Fin}\left(3\right))\right)), \forall (x : \operatorname{EuclideanSpace}\left(\mathbb{R}, (\operatorname{Fin}\left(3\right))\right)), (\forall (i : \operatorname{Fin}\left((N + 1)\right)), 0 < \operatorname{lam}\left(i\right)) \Rightarrow ((0 < mu) \Rightarrow ((\operatorname{Function.Injective}\left(a\right)) \Rightarrow ((\forall (i : \operatorname{Fin}\left((N + 1)\right)), x \ne \operatorname{a}\left(i\right)) \Rightarrow (0 < \operatorname{S}\left(lam, mu, (\lambda i \mapsto \operatorname{a}\left(i\right) - x)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/JNRRemarkThirteenPositivity.result` (`✓ std3`). ∎

*Resolves.* `Problems/cork-disney-hogg-2025-jnr-remark13-positivity` (proved) by `D5/S3/Analytic/JNRRemarkThirteenPositivity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cork-disney-hogg-2025-jnr-remark13-positivity","declaration_gid":"D5/S3/Analytic/JNRRemarkThirteenPositivity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Josh Cork and Linden Disney-Hogg (2025). *Locations of JNR skyrmions*. DOI: [10.1007/s11040-025-09513-3](https://doi.org/10.1007/s11040-025-09513-3). URL: <https://arxiv.org/abs/2505.00075v2>.

*Commentary.*

Set yᵢ = aᵢ − x, wᵢ = lam(i)², rᵢ = ‖yᵢ‖² and t = mu². Put αᵢ = wᵢ/(rᵢ+t), βᵢ = wᵢ/rᵢ and qᵢ = wᵢ/(rᵢ(rᵢ+t)); then βᵢ = αᵢ + t qᵢ. Let A = Σᵢ αᵢ, B = Σᵢ αᵢ yᵢ, C = Σᵢ βᵢ, D = Σᵢ βᵢ yᵢ and m = C⁻¹ D. Factoring the outer sums gives C S = Σⱼ qⱼ ⟨A yⱼ − B, C yⱼ − D⟩. The relation t Σᵢ qᵢ(yᵢ − m) = A m − B gives S = A Σᵢ qᵢ ‖yᵢ − m‖² + ‖A m − B‖²/t. Every coefficient is positive. Two distinct poles force a nonzero displacement from m, so the first term is positive and the second is nonnegative.

The private algebraic identities hold for every finite family in any real inner-product space. Strictness only needs two different vectors. For a constant family every original inner-product difference is zero; together these facts characterize the equality case. If D = 0, then m = 0 and the second square is ‖B‖²/t, which need not vanish. The conclusion concerns expression (18): equality with the source's earlier double sum away from (15), and physical realizations, are separate questions.

## References

- Truth anchor: `D5/S3/Analytic/JNRRemarkThirteenPositivity.S`
- Truth anchor: `D5/S3/Analytic/JNRRemarkThirteenPositivity.claim`
- Truth anchor: `D5/S3/Analytic/JNRRemarkThirteenPositivity.result`
- Truth anchor: `D5/S3/Analytic/JNRRemarkThirteenPositivity.rho0`
