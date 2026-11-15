# The exact deep-linear intrinsic-dimension prediction fails

## Abstract

Gaussian affine lines can miss the scalar deep-linear solution fiber.

**Definition 1.1 (sampleLaw).**

$$\forall (iota : Type), ([\operatorname{Fintype}\left(iota\right)], \forall (d : \mathbb{N}), (\operatorname{sampleLaw}\left(iota, d\right) = \operatorname{Measure}.\operatorname{prod}\left(\operatorname{Measure}.\operatorname{pi}\left(\operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(d\right), \operatorname{stdGaussian}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, iota\right)\right)\right)\right), \operatorname{stdGaussian}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, iota\right)\right)\right)))$$

*Formalization.* `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.sampleLaw` (`✓ std3`).

*Citation.* Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh (2026). *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*. DOI: [10.48550/arXiv.2610.39674](https://doi.org/10.48550/arXiv.2610.39674). URL: <https://arxiv.org/abs/2610.39674v1>.

*Commentary.*

Definition 1, page 5: “Equivalently, U is obtained by taking the column space of a p × d matrix with i.i.d. N (0, 1) entries or the kernel of a (p − d) × p matrix with i.i.d. N (0, 1) entries.” Each column and the offset are independent standard Gaussian vectors. The product includes the empty family at d = 0. The finite type iota indexes ambient coordinates. Function.const displays the constant Gaussian family indexed by Fin d.

**Definition 1.2 (affinePlane).**

$$\forall (iota : Type), ([\operatorname{Fintype}\left(iota\right)], \forall (d : \mathbb{N}), (\forall (z : (\operatorname{Fin}\left(d\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, iota\right)) \times (\operatorname{EuclideanSpace}\left(\mathbb{R}, iota\right))), (\operatorname{affinePlane}\left(d, z\right) = if d = \operatorname{Fintype}.\operatorname{card}\left(iota\right) then \operatorname{Set}.\operatorname{univ} else \{(x : \operatorname{EuclideanSpace}\left(\mathbb{R}, iota\right)) \mid x - z.2 \in \operatorname{Submodule}.\operatorname{span}\left(\mathbb{R}, \operatorname{Set}.\operatorname{range}\left(z.1\right)\right)\})))$$

*Formalization.* `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.affinePlane` (`✓ std3`).

*Citation.* Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh (2026). *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*. DOI: [10.48550/arXiv.2610.39674](https://doi.org/10.48550/arXiv.2610.39674). URL: <https://arxiv.org/abs/2610.39674v1>.

*Commentary.*

Definition 1, page 5: “If d = p, we set V = Rᵖ a.s.” Otherwise the set consists of x for which x minus the independent offset lies in the real span of the sampled columns. Translating by g or its orthogonal projection gives the same affine set.

**Definition 1.3 (intrinsicDimension).**

$$\forall (iota : Type), ([\operatorname{Fintype}\left(iota\right)], \forall (Theta : \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, iota\right)\right)), (\operatorname{intrinsicDimension}\left(Theta\right) = \operatorname{sInf}\left(\{(n : \mathbb{N}\infty) \mid \exists (d : \mathbb{N}), ((d \le \operatorname{Fintype}.\operatorname{card}\left(iota\right)) \land ((n = (d : \mathbb{N}\infty)) \land (\operatorname{sampleLaw}\left(iota, d\right)\left(\{(z : (\operatorname{Fin}\left(d\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, iota\right)) \times (\operatorname{EuclideanSpace}\left(\mathbb{R}, iota\right))) \mid \operatorname{Set}.\operatorname{Nonempty}\left(\operatorname{Set}.\operatorname{inter}\left(\operatorname{affinePlane}\left(d, z\right), Theta\right)\right)\}\right) = 1)))\}\right)))$$

*Formalization.* `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.intrinsicDimension` (`✓ std3`).

*Citation.* Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh (2026). *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*. DOI: [10.48550/arXiv.2610.39674](https://doi.org/10.48550/arXiv.2610.39674). URL: <https://arxiv.org/abs/2610.39674v1>.

*Commentary.*

Definition 2, page 5: “We define the intrinsic dimension” followed by equation (3). Its infimum is over integers d from zero through the ambient cardinality for which the displayed intersection event has probability one. The carrier is ENat, so an empty infimum is infinity; the displayed coercions send natural dimensions to ENat.

**Definition 1.4 (weight).**

$$\forall (L : \mathbb{N}), (\forall (m : \mathbb{N} \to \mathbb{N}), (\forall (theta : \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Sum}\left(\operatorname{Sigma}\left(fun (l : \operatorname{Fin}\left(L\right)) \mapsto (\operatorname{Fin}\left(\operatorname{m}\left(\operatorname{val}\left(l\right) + 1\right)\right)) \times (\operatorname{Fin}\left(\operatorname{m}\left(\operatorname{val}\left(l\right)\right)\right))\right), \operatorname{Fin}\left(\operatorname{m}\left(L\right)\right)\right)\right)), (\forall (l : \mathbb{N}), (\operatorname{weight}\left(theta, l\right) = fun (i : \operatorname{Fin}\left(\operatorname{m}\left(l + 1\right)\right)) \mapsto fun (j : \operatorname{Fin}\left(\operatorname{m}\left(l\right)\right)) \mapsto if h : l < L then \operatorname{theta}\left(\operatorname{Sum}.\operatorname{inl}\left(\langle \langle l, h\rangle, (i, j)\rangle\right)\right) else 0))))$$

*Formalization.* `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.weight` (`✓ std3`).

*Citation.* Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh (2026). *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*. DOI: [10.48550/arXiv.2610.39674](https://doi.org/10.48550/arXiv.2610.39674). URL: <https://arxiv.org/abs/2610.39674v1>.

*Commentary.*

Section 4.1, page 21: “We say h: Rᴹ⁰ → R is a function implemented by an L-layer deep linear network with architecture m = (M₀, . . . , Mᴸ) ∈ Nᴸ⁺¹ if there are weight matrices Wℓ ∈ Rᴹℓ×ᴹℓ⁻¹ and an ouput projection a ∈ Rᴹᴸ, for ℓ ∈ [L], such that h(x) = aᵀ Wᴸ Wᴸ₋₁ · · · W₁x.” The function m records the widths. Sum.inl indexes a matrix entry by a zero-based layer and its row and column; Sum.inr indexes the output projection. Only the layers below L contribute; unused indices return zero.

**Definition 1.5 (weightProduct).**

$$\forall (L : \mathbb{N}), (\forall (m : \mathbb{N} \to \mathbb{N}), (\forall (theta : \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Sum}\left(\operatorname{Sigma}\left(fun (l : \operatorname{Fin}\left(L\right)) \mapsto (\operatorname{Fin}\left(\operatorname{m}\left(\operatorname{val}\left(l\right) + 1\right)\right)) \times (\operatorname{Fin}\left(\operatorname{m}\left(\operatorname{val}\left(l\right)\right)\right))\right), \operatorname{Fin}\left(\operatorname{m}\left(L\right)\right)\right)\right)), ((\operatorname{weightProduct}\left(theta, 0\right) = 1) \land (\forall (l : \mathbb{N}), (\operatorname{weightProduct}\left(theta, l + 1\right) = \operatorname{weight}\left(theta, l\right) \cdot \operatorname{weightProduct}\left(theta, l\right))))))$$

*Formalization.* `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.weightProduct` (`✓ std3`).

*Citation.* Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh (2026). *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*. DOI: [10.48550/arXiv.2610.39674](https://doi.org/10.48550/arXiv.2610.39674). URL: <https://arxiv.org/abs/2610.39674v1>.

*Commentary.*

The ordered product has identity at zero and left-multiplies by the next weight matrix at a successor. Thus weightProduct theta L is Wᴸ · · · W₁, with no reversal of the matrix order.

**Definition 1.6 (realization).**

$$\forall (L : \mathbb{N}), (\forall (m : \mathbb{N} \to \mathbb{N}), (\forall (theta : \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Sum}\left(\operatorname{Sigma}\left(fun (l : \operatorname{Fin}\left(L\right)) \mapsto (\operatorname{Fin}\left(\operatorname{m}\left(\operatorname{val}\left(l\right) + 1\right)\right)) \times (\operatorname{Fin}\left(\operatorname{m}\left(\operatorname{val}\left(l\right)\right)\right))\right), \operatorname{Fin}\left(\operatorname{m}\left(L\right)\right)\right)\right)), (\operatorname{realization}\left(theta\right) = \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{Matrix}.\operatorname{transpose}\left(\operatorname{weightProduct}\left(theta, L\right)\right), fun (i : \operatorname{Fin}\left(\operatorname{m}\left(L\right)\right)) \mapsto \operatorname{theta}\left(\operatorname{Sum}.\operatorname{inr}\left(i\right)\right)\right))))$$

*Formalization.* `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.realization` (`✓ std3`).

*Citation.* Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh (2026). *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*. DOI: [10.48550/arXiv.2610.39674](https://doi.org/10.48550/arXiv.2610.39674). URL: <https://arxiv.org/abs/2610.39674v1>.

*Commentary.*

Equation (20), page 22, uses W₁ᵀ W₂ᵀ · · · Wᴸᵀ a. This is the transpose of the ordered product applied to the output coordinates. All matrices and vectors are real.

**Definition 1.7 (solutionSet).**

$$\forall (L : \mathbb{N}), (\forall (m : \mathbb{N} \to \mathbb{N}), (\forall (u : \operatorname{Fin}\left(\operatorname{m}\left(0\right)\right) \to \mathbb{R}), (\operatorname{solutionSet}\left((L := L), (m := m), u\right) = \{(theta : \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Sum}\left(\operatorname{Sigma}\left(fun (l : \operatorname{Fin}\left(L\right)) \mapsto (\operatorname{Fin}\left(\operatorname{m}\left(\operatorname{val}\left(l\right) + 1\right)\right)) \times (\operatorname{Fin}\left(\operatorname{m}\left(\operatorname{val}\left(l\right)\right)\right))\right), \operatorname{Fin}\left(\operatorname{m}\left(L\right)\right)\right)\right)) \mid \operatorname{realization}\left(theta\right) = u\})))$$

*Formalization.* `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.solutionSet` (`✓ std3`).

*Citation.* Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh (2026). *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*. DOI: [10.48550/arXiv.2610.39674](https://doi.org/10.48550/arXiv.2610.39674). URL: <https://arxiv.org/abs/2610.39674v1>.

*Commentary.*

Equation (20), page 22: Θ = {(W₁, . . . , Wᴸ, a) : W₁ᵀ W₂ᵀ · · · Wᴸᵀ a = u⋆}. These are the bias-free coordinates of that tuple and of Theorem 17. The paragraph following equation (20) contains bias coordinates inconsistent with this displayed tuple; they are not coordinates of the displayed polynomial fiber.

**Definition 1.8 (claim).**

$$claim \Leftrightarrow (\forall (L : \mathbb{N}), (\forall (m : \mathbb{N} \to \mathbb{N}), ((1 \le L) \Rightarrow ((\forall (l : \mathbb{N}), ((l \le L) \Rightarrow (1 \le \operatorname{m}\left(l\right)))) \Rightarrow (\forall (u : \operatorname{Fin}\left(\operatorname{m}\left(0\right)\right) \to \mathbb{R}), ((u \ne 0) \Rightarrow (\operatorname{intrinsicDimension}\left(\operatorname{solutionSet}\left((L := L), (m := m), u\right)\right) = (\operatorname{m}\left(0\right) : \mathbb{N}\infty))))))))$$

*Formalization.* `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.claim` (`✓ std3`).

*Citation.* Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh (2026). *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*. DOI: [10.48550/arXiv.2610.39674](https://doi.org/10.48550/arXiv.2610.39674). URL: <https://arxiv.org/abs/2610.39674v1>.

*Commentary.*

Page 23: “As we will see in Section 7, numerical experiments suggest that dᵢₙₜ(Θ) = D in the deep linear case independently of the width and depth of the network.” Here L is positive, every m l for l at most L is positive, D is m 0, and the target u is nonzero. The ambient coordinate type has one coordinate for each weight entry and each output entry. The assertion quantifies all these architectures and targets.

**Theorem 1.9 (Negation of the complete exact-value prediction).**

$$\neg (\forall (L : \mathbb{N}), (\forall (m : \mathbb{N} \to \mathbb{N}), ((1 \le L) \Rightarrow ((\forall (l : \mathbb{N}), ((l \le L) \Rightarrow (1 \le \operatorname{m}\left(l\right)))) \Rightarrow (\forall (u : \operatorname{Fin}\left(\operatorname{m}\left(0\right)\right) \to \mathbb{R}), ((u \ne 0) \Rightarrow (\operatorname{intrinsicDimension}\left(\operatorname{solutionSet}\left((L := L), (m := m), u\right)\right) = (\operatorname{m}\left(0\right) : \mathbb{N}\infty))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/araya-kutyniok-li-maly-singh-intrinsic-dimension` (refuted) by `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"araya-kutyniok-li-maly-singh-intrinsic-dimension","declaration_gid":"D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ernesto Araya, Gitta Kutyniok, Weilin Li, Johannes Maly and Manjot Singh (2026). *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*. DOI: [10.48550/arXiv.2610.39674](https://doi.org/10.48550/arXiv.2610.39674). URL: <https://arxiv.org/abs/2610.39674v1>.

*Commentary.*

Take L = 1, every width equal to one, and target u = 1. The fiber is the hyperbola wa = 1. A sampled point with wa < 1 misses it. For a sampled line g + tv, its intersection equation has coefficients A = v₁v₂, B = g₁v₂ + v₁g₂, and C = g₁g₂ − 1. The open region A < 0 with negative discriminant contains v = (1, −1), g = 0, so Gaussian full support gives it positive measure. The quadratic equation has no real root there. Hence neither dimension zero nor dimension one has intersection probability one. The infimum is at least two, contradicting the asserted value one. This argument proves a global affine-intersection obstruction; it does not evaluate general widths or depths.

## References

- Truth anchor: `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.affinePlane`
- Truth anchor: `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.intrinsicDimension`
- Truth anchor: `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.realization`
- Truth anchor: `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.result`
- Truth anchor: `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.sampleLaw`
- Truth anchor: `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.solutionSet`
- Truth anchor: `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.weight`
- Truth anchor: `D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.weightProduct`
