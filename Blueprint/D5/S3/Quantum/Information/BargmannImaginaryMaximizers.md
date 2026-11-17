# All qubit maximizers of the imaginary Bargmann invariant

## Abstract

For every n at least three, the unit qubit tuples with imaginary Bargmann invariant tau n form one unitary orbit of a latitude polygon, allowing an independent phase at each vertex.

**Theorem 1.1 (An upper bound for a finite weighted mean).**

$$\forall (\iota : \operatorname{Type}*), [\operatorname{Fintype}\left(\iota\right)] \forall (w : (\iota) \to (\mathbb{R})), \forall (c : (\iota) \to (\mathbb{R})), \forall (M : \mathbb{R}), (\forall (k : \iota), (0 : \mathbb{R}) \le w\left(k\right)) \Rightarrow ((\sum_{k : \iota} (w\left(k\right)) = (1 : \mathbb{R})) \Rightarrow ((\forall (k : \iota), c\left(k\right) \le M) \Rightarrow ((\sum_{k : \iota} (c\left(k\right) \cdot w\left(k\right)) \le M) \land ((\sum_{k : \iota} (c\left(k\right) \cdot w\left(k\right)) = M) \Leftrightarrow (\forall (k : \iota), (c\left(k\right) < M) \Rightarrow (w\left(k\right) = (0 : \mathbb{R})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.weighted_edge_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative weights of total mass one preserve a common upper bound; equality holds exactly when every term strictly below the bound has zero weight.

**Definition 1.2 (A qubit latitude vector).**

$$\forall (t : \mathbb{R}), \forall (z : \mathbb{C}), \operatorname{Latitude.latitude}\left(t, z\right) = ![(\operatorname{Real.sqrt}\left(1 - t\right) : \mathbb{C}), (\operatorname{Real.sqrt}\left(t\right) : \mathbb{C}) \cdot z]$$

*Formalization.* `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.latitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two coordinates have square-root amplitudes, with a complex factor on the second coordinate.

**Theorem 1.3 (Inner products of latitude vectors).**

$$\forall (t : \mathbb{R}), (0 \le t) \Rightarrow ((t \le 1) \Rightarrow (\forall (z : \mathbb{C}), \forall (w : \mathbb{C}), \operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{Latitude.latitude}\left(t, z\right)\right), \operatorname{Latitude.latitude}\left(t, w\right)\right) = (1 - t : \mathbb{C}) + (t : \mathbb{C}) \cdot \operatorname{star}\left(z\right) \cdot w))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.latitude_dot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a latitude parameter between zero and one, the inner product is the sum of the two coordinate contributions.

Vectors have type Fin 2 → ℂ. For a unit vector v, Matrix.vecMulVec v (star v) is its rank-one projector. Indices have type Fin n and start at zero. List.ofFn lists the outer products in increasing index order and List.prod takes their ordered matrix product. Real division, the real square root and natural powers have Lean's total meanings; the exponent n − 1 is natural subtraction, whereas the denominator 2 · (n − 1) uses real subtraction after coercing n to ℝ.

**Definition 1.4 (Ordered trace of pure states).**

$$\forall (n : \mathbb{N}), \forall (\psi : (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{C}))), \operatorname{bargmann}\left(\psi\right) = \operatorname{Matrix.trace}\left(\operatorname{List.prod}\left(\operatorname{List.ofFn}\left(\operatorname{fun} (j : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{Matrix.vecMulVec}\left(\psi\left(j\right), \operatorname{star}\left(\psi\left(j\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.bargmann` (`✓ std3`).

*Citation.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

Zhang and Xie, Definition 3.1, p. 9: “The so-called nth-order Bargmann invariant for such n-tuple Ψ = (ρ₁, …, ρₙ) is defined as Δₙ(Ψ) := Tr(ρ₁ ⋯ ρₙ).” Section 2, p. 4: “Unit vector |ψ⟩ in ℂ^d will be called wave functions and its ranked-one projector ψ ≡ |ψ⟩⟨ψ| will be called pure state.” Here d = 2 and each ρ is the displayed outer product of its amplitude vector with its conjugate.

**Theorem 1.5 (The overlap product of an ordered rank-one chain).**

$$\forall (n : \mathbb{N}), \forall (\psi : (\operatorname{Fin}\left(n + 1\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{C}))), \operatorname{bargmann}\left(\psi\right) = (\prod_{j : \operatorname{Fin}\left(n\right)} (\operatorname{dotProduct}\left(\operatorname{star}\left(\psi\left(\operatorname{Fin.castSucc}\left(j\right)\right)\right), \psi\left(\operatorname{Fin.succ}\left(j\right)\right)\right))) \cdot (\operatorname{dotProduct}\left(\operatorname{star}\left(\psi\left(\operatorname{Fin.last}\left(n\right)\right)\right), \psi\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.bargmann_path_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every tuple Ψ of n + 1 arbitrary vectors in ℂ², the trace of their ordered outer-product chain is the product of the n consecutive inner products, followed by the closing inner product from the last vector to the first. The inner product convention is ⟨u, v⟩ = star u dotProduct v. No normalization or nonzero premise is imposed; an outer product may therefore be zero. For n = 0, the empty consecutive product is one and the closing factor is ⟨Ψ₀, Ψ₀⟩, the trace of the single outer product.

For an ideal finite polarizer cascade, let vⱼ = v(αⱼ) = (cos αⱼ, sin αⱼ), embedded from ℝ² into ℂ², and Pⱼ = vⱼvⱼ†, for j = 0, …, m. These vectors are unit vectors. Starting from the prepared state P₀, the branch that passes every subsequent filter has Kₘ = Pₘ⋯P₁ and unnormalized state Xₘ = KₘP₀Kₘ† = Pₘ⋯P₁P₀P₁⋯Pₘ. Its weight is Tr(Xₘ). Apply bargmann_path_product with n = 2m to the ordered vector tuple (vₘ, …, v₁, v₀, v₁, …, vₘ). Each consecutive overlap is paired with its complex conjugate, while the closing overlap is ⟨vₘ, vₘ⟩ = 1. Thus Tr(Xₘ) = ∏ⱼ₌₁ᵐ |⟨vⱼ, vⱼ₋₁⟩|² = ∏ⱼ₌₁ᵐ cos²(αⱼ − αⱼ₋₁). This is the trace of one ordered success branch; it requires no independence assumption on successive outcomes.

For N intermediate filters between horizontal and vertical polarization, take N to be a natural number, including zero, and put m = N + 1 > 0 and αⱼ = jπ/(2m). All angles are real and measured in radians. The finite all-through weight relative to the prepared horizontal input is w_N = [cos²(π/(2m))]ᵐ = [cos²(π/(2(N + 1)))]ᴺ⁺¹. N = 0 gives zero and N = 1 gives 1/4. For unpolarized input I/2, retaining the initial horizontal preparation contributes a separate factor 1/2 to the weight relative to that input.

Analytic application of existing Mathlib. Define f : ℝ → ℝ by f(x) = cos((π/2)x)². Then f(0) = 1, and the chain and power rules give f′(x) = −π sin((π/2)x) cos((π/2)x), hence f′(0) = 0. The reused derivative declarations are Real.hasDerivAt_cos, HasDerivAt.const_mul, HasDerivAt.cos and HasDerivAt.fun_pow. HasDerivAt.tendsto_slope_zero_right (Mathlib/Analysis/Calculus/Deriv/Slope.lean) therefore gives x⁻¹(f(0 + x) − f(0)) = (f(x) − 1)/x → 0 as x → 0 from the right.

Compose this slope limit with tendsto_inv_atTop_nhdsGT_zero and tendsto_natCast_atTop_atTop: x = (n : ℝ)⁻¹ tends to zero from the right as the natural number n tends to infinity. For n > 0 the slope at that x equals (n : ℝ)(f((n : ℝ)⁻¹) − 1), so this last expression tends to zero. Set g(n) = f((n : ℝ)⁻¹) − 1 and t = 0 in Real.tendsto_one_add_pow_exp_of_tendsto (Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean). Its hypothesis is exactly (n : ℝ)g(n) → t, and its conclusion is (1 + g(n))ⁿ → exp(t). Here 1 + g(n) = f((n : ℝ)⁻¹), so [cos²(π/(2n))]ⁿ → exp(0) = 1. The auxiliary sequence at n = 0 uses Lean's total real inverse and natural power; only its eventually positive tail is used in the slope substitution.

Finally tendsto_add_atTop_nat 1 shifts n to N + 1 = m. Thus w_N = [cos²(π/(2(N + 1)))]ᴺ⁺¹ → 1 as N → ∞. Multiplication by the constant 1/2, using Filter.Tendsto.const_mul, gives (1/2)w_N → 1/2 for the weight relative to unpolarized input when the initial horizontal preparation is retained. The limit one refers to the prepared horizontal input; the preparation factor remains separate.

The finite cascade and the analytic application use ideal rank-one projections and require no independence premise. The analytic limit is an application of the cited Mathlib results, outside the Lean statement of bargmann_path_product. Scalar strict increase with N is a separate monotonicity assertion, not established by this application. Real attenuation is outside the model; these ideal formulas imply no transmission limit for general noisy filters or absorbing media.

**Definition 1.6 (The maximal imaginary value).**

$$\forall (n : \mathbb{N}), \operatorname{tau}\left(n\right) = \frac{\operatorname{Real.cos}\left(\frac{\operatorname{Real.pi}}{(n : \mathbb{R})}\right)^{n}}{\operatorname{Real.cos}\left(\frac{\operatorname{Real.pi}}{2 \cdot ((n : \mathbb{R}) - 1)}\right)^{(n - 1)}}$$

*Formalization.* `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.tau` (`✓ std3`).

*Citation.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

Zhang and Xie, Corollary 5.5, p. 25, Eq. (5.15): “τₙ := cosⁿ(π/n) secⁿ⁻¹(π/[2(n−1)]).” The reciprocal cosine power expresses the secant power; the classification below concerns n ≥ 3.

**Definition 1.7 (The latitude polygon).**

$$\forall (n : \mathbb{N}), \forall (j : \operatorname{Fin}\left(n\right)), \operatorname{let} (t : \mathbb{R}) := \frac{1 - \frac{\operatorname{Real.tan}\left(\frac{\operatorname{Real.pi}}{2 \cdot ((n : \mathbb{R}) - 1)}\right)}{\operatorname{Real.tan}\left(\frac{\operatorname{Real.pi}}{(n : \mathbb{R})}\right)}}{2}; \operatorname{maximizer}\left(n, j\right) = ![(\operatorname{Real.sqrt}\left(1 - t\right) : \mathbb{C}), (\operatorname{Real.sqrt}\left(t\right) : \mathbb{C}) \cdot \operatorname{Complex.exp}\left(\frac{2 \cdot (\operatorname{Real.pi} : \mathbb{C}) \cdot \operatorname{Complex.I} \cdot (\operatorname{val}\left(j\right) : \mathbb{C})}{(n : \mathbb{C})}\right)]$$

*Formalization.* `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.maximizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

The jth vector is (√(1 − t), √t · exp(2πij/n)), with t = (1 − tan(π/[2(n−1)])/tan(π/n))/2. The square roots are embedded from ℝ into ℂ. For n ≥ 3 the weight t lies strictly between zero and one half. The last coordinate uses the complex coercions of j and n.

**Definition 1.8 (The complete set of maximizing tuples).**

$$\operatorname{claim} = (\forall (n : \mathbb{N}), (3 \le n) \Rightarrow (\forall (\psi : (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{C}))), (\forall (j : \operatorname{Fin}\left(n\right)), \operatorname{dotProduct}\left(\operatorname{star}\left(\psi\left(j\right)\right), \psi\left(j\right)\right) = 1) \Rightarrow ((\operatorname{Complex.im}\left(\operatorname{bargmann}\left(\psi\right)\right) = \operatorname{tau}\left(n\right)) \Leftrightarrow (\exists (U : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land (\exists (eta : (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), (\forall (j : \operatorname{Fin}\left(n\right)), \left\lVert eta\left(j\right) \right\rVert = 1) \land (\forall (j : \operatorname{Fin}\left(n\right)), \psi\left(j\right) = \operatorname{SMul.smul}\left(eta\left(j\right), \operatorname{Matrix.mulVec}\left(U, \operatorname{maximizer}\left(n, j\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

Zhang and Xie, p. 26: “The quantity τ_n predicts the upper bound for the imaginary part of any nth-order Bargmann invariant. This immediately raises the question: what is the complete set of n-tuples Ψ = (|ψ_1⟩, …, |ψ_n⟩) in ℂ² that achieve Im Tr(ψ_1 … ψ_n) = τ_n? We leave this characterization, along with the operational interpretation of the condition z ∈ 𝓑_{n+1} ∖ 𝓑_n, as interesting open problems for future work.” The displayed answer uses one common matrix U in Matrix.unitaryGroup and independent complex phases eta of norm one. The wave-function premise is star (Ψ j) dotProduct (Ψ j) = 1. The second question is outside this equivalence.

**Theorem 1.9 (Classification of every maximizing qubit tuple).**

$$\forall (n : \mathbb{N}), (3 \le n) \Rightarrow (\forall (\psi : (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(2\right)) \to (\mathbb{C}))), (\forall (j : \operatorname{Fin}\left(n\right)), \operatorname{dotProduct}\left(\operatorname{star}\left(\psi\left(j\right)\right), \psi\left(j\right)\right) = 1) \Rightarrow ((\operatorname{Complex.im}\left(\operatorname{bargmann}\left(\psi\right)\right) = \operatorname{tau}\left(n\right)) \Leftrightarrow (\exists (U : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (U \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land (\exists (eta : (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), (\forall (j : \operatorname{Fin}\left(n\right)), \left\lVert eta\left(j\right) \right\rVert = 1) \land (\forall (j : \operatorname{Fin}\left(n\right)), \psi\left(j\right) = \operatorname{SMul.smul}\left(eta\left(j\right), \operatorname{Matrix.mulVec}\left(U, \operatorname{maximizer}\left(n, j\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-xie-2026-bargmann-imaginary-maximizers` (proved) by `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-xie-2026-bargmann-imaginary-maximizers","declaration_gid":"D5/S3/Quantum/Information/BargmannImaginaryMaximizers.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang; Bing Xie (2026). *A Survey of Bargmann Invariants: Geometric Foundations and Applications*. DOI: [10.48550/arXiv.2601.01858](https://doi.org/10.48550/arXiv.2601.01858). URL: <https://arxiv.org/abs/2601.01858v2>.

*Commentary.*

Rephase consecutive overlaps onto one ray. AM–GM compares their product with their mean, and the exposed edge of the regular polygon of Fourier phases bounds that mean. Equality at the unique scalar maximum removes every Fourier mode except zero and one. Parseval's energy identity and unit length at two vertices force these two modes to be orthogonal. Their Gram matrix determines a common unitary, and the mean overlap fixes the latitude weight. Conversely, the polygon has constant consecutive overlap and its ordered trace has imaginary part tau n; unitary transformations and the individual phases preserve that trace.

## References

- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.bargmann`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.bargmann_path_product`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.claim`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.latitude`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.latitude_dot`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.maximizer`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.result`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.tau`
- Truth anchor: `D5/S3/Quantum/Information/BargmannImaginaryMaximizers.weighted_edge_bound`
- Dependency: [D5/S3/Quantum/Algebra/GramUnitaryExtension](../Algebra/GramUnitaryExtension.md)
