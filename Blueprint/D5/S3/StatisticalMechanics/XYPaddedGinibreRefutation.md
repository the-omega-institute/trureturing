# The XY model violates a padded Ginibre inequality

## Abstract

The XY model violates a padded general Ginibre inequality on a five-cycle.

**Definition 1.1 (The free O(2) probability measure).**

$$\forall p: \mathbb{N}, \operatorname{freeMeasure}\left(p\right) = \operatorname{Measure}.\operatorname{pi}\left(\operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(p\right), \operatorname{AddCircle}.\operatorname{haarAddCircle}\left(2 \cdot \operatorname{Real}.\operatorname{pi}\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.freeMeasure` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 2: "The free measure μ is the product of copies of the unique O(N)-invariant Borel probability measure on the sphere Sᴺ⁻¹." Here N = 2. The rotation-invariant probability measure on S¹ is the image of normalized Haar measure on angles under θ ↦ (cos θ, sin θ). The carrier Real.Angle is Mathlib's AddCircle (2 * Real.pi), and freeMeasure p is the product measure on Fin p → Real.Angle. AddCircle.haarAddCircle has total mass one; the displayed argument is its implicit period 2 * Real.pi, and its positivity proof is Real.two_pi_pos. Function.const supplies the same angle measure at every site.

**Definition 1.2 (Unit spins in angle coordinates).**

$$\forall \theta: \operatorname{Real}.\operatorname{Angle}, \operatorname{spin}\left(\theta\right) = [\operatorname{Real}.\operatorname{Angle}.\operatorname{cos}\left(\theta\right),\operatorname{Real}.\operatorname{Angle}.\operatorname{sin}\left(\theta\right)]$$

*Formalization.* `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.spin` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 2: "Each spin σᵢ is a column vector (σᵢ,₁,…,σᵢ,ᴺ)ᵀ in Sᴺ⁻¹, i.e., which satisfies Σ_{ℓ=1}ᴺ σᵢ,ℓ² = 1." With N = 2 the vector spin θ has coordinates cos θ and sin θ, in this order. The displayed vector is the Lean vector notation ![Real.Angle.cos θ, Real.Angle.sin θ], a function Fin 2 → ℝ. The identity cos² θ + sin² θ = 1 makes it a unit spin.

**Definition 1.3 (Pair observables).**

$$\forall p: \mathbb{N}, \forall x: \operatorname{Fin}\left(p\right) \to \operatorname{Real}.\operatorname{Angle}, \forall e: \{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\}, \operatorname{observable}\left(x, e\right) = \operatorname{dotProduct}\left(\operatorname{spin}\left(x\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{val}\left(e\right)\right)\right)\right), \operatorname{spin}\left(x\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{val}\left(e\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.observable` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 2: "The basic observables are the inner products σᵢ·σᵢ′ := Σ_{ℓ=1}ᴺ σᵢ,ℓ σᵢ′,ℓ, with 1 ≤ i < i′ ≤ p." Fin indices are zero-based. All pairs are represented by the subtype {e : Fin p × Fin p // e.1 < e.2}; val is the existing Subtype.val projection. Mathlib dotProduct is the sum of the two products of spin coordinates.

**Definition 1.4 (Observable monomials).**

$$\forall p: \mathbb{N}, \forall u: \{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\} \to \mathbb{N}, \forall x: \operatorname{Fin}\left(p\right) \to \operatorname{Real}.\operatorname{Angle}, \operatorname{monomial}\left(u, x\right) = \prod_{e:\{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\}} \operatorname{observable}\left(x, e\right)^{u\left(e\right)}$$

*Formalization.* `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.monomial` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 2: "we will write 𝒪(x)^a or just 𝒪^a for the monomial 𝒪₁(x)^a₁ ⋯ 𝒪ₙ(x)^aₙ in the basic observables." The natural multiindex is called u in monomial. The product ranges over every pair i < j, including pairs whose exponent is zero. Both x and u retain the same pair and site carriers as observable.

**Definition 1.5 (The endpoint parity homomorphism).**

$$\forall p: \mathbb{N}, \forall a: \{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\} \to \mathbb{Z}, \forall i: \operatorname{Fin}\left(p\right), \operatorname{parity}\left(p\right)\left(a, i\right) = \sum_{e:\{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\}} (\operatorname{ite}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{val}\left(e\right)\right) = i, (a\left(e\right)):\operatorname{ZMod}\left(2\right), 0\right) + \operatorname{ite}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{val}\left(e\right)\right) = i, (a\left(e\right)):\operatorname{ZMod}\left(2\right), 0\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.parity` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 5: "In the case of the O(N) model as described above, we take L = p and for j corresponding to a pair of vertices (i,i′), with 1 ≤ i < i′ ≤ p, we define ρ(eⱼ) as the vector with all components equal to 0 except the i'-th and i′-th components which are set equal to 1." The integer multiindex a contributes a(e) modulo two at both endpoints of each pair e. The displayed evaluation specifies parity p as an additive homomorphism from integer pair-indices to Fin p → ZMod 2; ite is the ordinary conditional expression.

**Definition 1.6 (The padded general Ginibre functional).**

$$\forall p: \mathbb{N}, \forall m: \mathbb{N}, \forall V: \operatorname{Fin}\left(m\right) \to \{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\} \to \mathbb{N}, \forall \varepsilon: \operatorname{Fin}\left(m\right) \to \mathbb{R}, \forall u: \{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\} \to \mathbb{N}, \operatorname{pgg}\left(V, \varepsilon, u\right) = \int_{xy:(\operatorname{Fin}\left(p\right) \to \operatorname{Real}.\operatorname{Angle}) \times (\operatorname{Fin}\left(p\right) \to \operatorname{Real}.\operatorname{Angle})} \operatorname{monomial}\left(u, \operatorname{Prod}.\operatorname{fst}\left(xy\right)\right) \cdot \operatorname{monomial}\left(u, \operatorname{Prod}.\operatorname{snd}\left(xy\right)\right) \cdot (\prod_{i:\operatorname{Fin}\left(m\right)} (\operatorname{monomial}\left(V\left(i\right), \operatorname{Prod}.\operatorname{fst}\left(xy\right)\right) + \varepsilon\left(i\right) \cdot \operatorname{monomial}\left(V\left(i\right), \operatorname{Prod}.\operatorname{snd}\left(xy\right)\right))) \operatorname{d}(\operatorname{Measure}.\operatorname{prod}\left(\operatorname{freeMeasure}\left(p\right), \operatorname{freeMeasure}\left(p\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.pgg` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 6: "We will say that the system (X, μ, 𝒪, L, ρ) satisfies the PGG collection of inequalities iff ∀ m ≥ 0, ∀ V ∈ ℕᵐˣⁿ, ∀ (ε₁,…,εₘ) ∈ {−1,1}ᵐ, and all even u ∈ ℕⁿ we have" the duplicated integral at least zero. The displayed definition is that integral before the inequality. Rows V i and padding u are natural pair-indices. The integral is over two independent configurations using Measure.prod (freeMeasure p) (freeMeasure p); Prod.fst and Prod.snd project the two configurations. The finite product ranges over Fin m and is one when m = 0.

**Definition 1.7 (Problem 2: the XY-PGG assertion).**

$$(claim) \Leftrightarrow (\forall p: \mathbb{N}, (0 < p) \Rightarrow (\forall m: \mathbb{N}, \forall V: \operatorname{Fin}\left(m\right) \to \{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\} \to \mathbb{N}, \forall \varepsilon: \operatorname{Fin}\left(m\right) \to \mathbb{R}, \forall u: \{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\} \to \mathbb{N}, (\forall i: \operatorname{Fin}\left(m\right), (\varepsilon\left(i\right) = -1) \lor (\varepsilon\left(i\right) = 1)) \Rightarrow ((\operatorname{parity}\left(p\right)\left(e:\{e:\operatorname{Fin}\left(p\right) \times \operatorname{Fin}\left(p\right)\mid\operatorname{Prod}.\operatorname{fst}\left(e\right) < \operatorname{Prod}.\operatorname{snd}\left(e\right)\}\mapsto(u\left(e\right)):\mathbb{Z}\right) = 0) \Rightarrow (0 \le \operatorname{pgg}\left(V, \varepsilon, u\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.claim` (`✓ std3`).

*Citation.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Page 14: "For the XY model, or O(2) model, the GG inequalities were proved by Ginibre [18]. What about the padded generalizations given by the PGG inequalities?" The displayed claim asks for the PGG collection on every p ≥ 1 sites. It retains every quantifier from p. 6: m is any natural number, V has natural entries on all pairs, every real ε i is −1 or 1, and u is any even natural multiindex. Page 5: "We will say that a is even iff ρ(a) = 0." The inline condition casts u coordinatewise to integers before applying parity p; zero is the zero function Fin p → ZMod 2. No condition that the sum of the rows of V be even is imposed in this definition of the PGG collection. The angle measure convention is stated above.

**Theorem 1.8 (The XY-PGG assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Abdelmalek Abdesselam (2022). *Non-Abelian correlation inequalities and stable determinantal polynomials*. DOI: [10.48550/arXiv.2207.07603](https://doi.org/10.48550/arXiv.2207.07603). URL: <https://arxiv.org/abs/2207.07603v2>.

*Commentary.*

Take p = 5 and the five pairs (0,1), (1,2), (2,3), (3,4), (0,4). Let u be their indicator, m = 2, both rows V i = u, and both signs ε i = −1. Each vertex is incident to two chosen pairs, so u is even. Set Z(x) to the product of the five pair observables. Fourier orthogonality on each angle forces every surviving edge frequency to be constant around the cycle. Applying this to the first three powers gives M₁ = E[Z] = 1/16, M₂ = E[Z²] = 17/512 and M₃ = E[Z³] = 61/4096. The duplicated functional is E[Z(x)Z(y)(Z(x) − Z(y))²] = 2(M₁M₃ − M₂²) = −45/131072 < 0. The square factor is nonnegative, but the padding product Z(x)Z(y) can be negative; the exact moments show that its negative contribution prevails.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.freeMeasure`
- Truth anchor: `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.monomial`
- Truth anchor: `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.observable`
- Truth anchor: `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.parity`
- Truth anchor: `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.pgg`
- Truth anchor: `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.spin`
