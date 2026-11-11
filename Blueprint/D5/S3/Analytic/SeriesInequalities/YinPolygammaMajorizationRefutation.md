# Finite Polygamma Majorization Refutation

## Abstract

A strict finite-moment gap and equal endpoint limits refute finite polygamma majorization monotonicity.

**Definition 1.1 (Finite digamma).**

$$\forall p \in \mathbb{N},\; \forall k \in \mathbb{R},\; \forall x \in \mathbb{R},\; \operatorname{psi}\left(p, k, x\right) = \frac{1}{k} \cdot \operatorname{Real.log}\left((\operatorname{Nat.cast}\left(p\right): \mathbb{R}) \cdot k\right) - \sum_{j\in \operatorname{Finset.range}\left(p + 1\right)} (\frac{1}{(\operatorname{Nat.cast}\left(j\right): \mathbb{R}) \cdot k + x})$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.psi` (`✓ std3`).

*Citation.* Li Yin (2022). *Monotonic properties for ratio of the generalized (p,k)-polygamma functions*. DOI: [10.7153/jmi-2022-16-62](https://doi.org/10.7153/jmi-2022-16-62). URL: <https://files.ele-math.com/articles/jmi-16-62.pdf>.

*Commentary.*

Equation (1.5), p. 916, defines ψₚ,ₖ(x) = (1/k) ln(pk) − ∑ⱼ₌₀ᵖ 1/(jk+x). The index p is a positive integer and k and x are positive reals in the source domain; the Lean function is total on all real arguments.

**Definition 1.2 (Derivatives of the finite digamma).**

$$\forall p \in \mathbb{N},\; \forall k \in \mathbb{R},\; \forall m \in \mathbb{N},\; \forall x \in \mathbb{R},\; \operatorname{polygamma}\left(p, k, m, x\right) = \operatorname{iteratedDeriv}\left(m, \operatorname{psi}\left(p, k\right), x\right)$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.polygamma` (`✓ std3`).

*Citation.* Li Yin (2022). *Monotonic properties for ratio of the generalized (p,k)-polygamma functions*. DOI: [10.7153/jmi-2022-16-62](https://doi.org/10.7153/jmi-2022-16-62). URL: <https://files.ele-math.com/articles/jmi-16-62.pdf>.

*Commentary.*

The sentence before (1.5), p. 916, defines “ψₚ,ₖ⁽ᵐ⁾(x) = dᵐ/dxᵐ ψₚ,ₖ(x).” Mathlib iteratedDeriv expresses this derivative. For positive order r its value is (−1)ʳ⁺¹ r! times the sum of (jk+x)⁻ʳ⁻¹. The finite-sum sign printed in (1.6) differs from differentiation of (1.5); the derivative definition is used here.

**Definition 1.3 (Strict majorization of the order tuples).**

$$\forall n \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall b \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \operatorname{StrictlyMajorized}\left(a, b\right)\iff ((\operatorname{D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.moreMixed}\left(\operatorname{fun} i: \operatorname{Fin}\left(n\right) \mapsto (\operatorname{Nat.cast}\left(a\left(i\right)\right): \mathbb{R}), \operatorname{fun} i: \operatorname{Fin}\left(n\right) \mapsto (\operatorname{Nat.cast}\left(b\left(i\right)\right): \mathbb{R})\right)) \land (\operatorname{D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.desc}\left(\operatorname{fun} i: \operatorname{Fin}\left(n\right) \mapsto (\operatorname{Nat.cast}\left(a\left(i\right)\right): \mathbb{R})\right) \ne \operatorname{D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.desc}\left(\operatorname{fun} i: \operatorname{Fin}\left(n\right) \mapsto (\operatorname{Nat.cast}\left(b\left(i\right)\right): \mathbb{R})\right)))$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.StrictlyMajorized` (`✓ std3`).

*Citation.* Li Yin (2022). *Monotonic properties for ratio of the generalized (p,k)-polygamma functions*. DOI: [10.7153/jmi-2022-16-62](https://doi.org/10.7153/jmi-2022-16-62). URL: <https://files.ele-math.com/articles/jmi-16-62.pdf>.

*Commentary.*

Page 916: “Let α=(α₁,α₂,⋯,αₙ) and β=(β₁,β₂,⋯,βₙ)∈ℝⁿ. A n-tuple α is said to strictly majorize β (in symbols α≻β) if (α[1],α[2],⋯,α[n])≠(β[1],β[2],⋯,β[n]), ∑ᵢ₌₁ᵏ α[i]≥∑ᵢ₌₁ᵏ β[i] for 1≤k≤n−1, and ∑ᵢ₌₁ⁿ αᵢ=∑ᵢ₌₁ⁿ βᵢ where α[1]≥α[2]≥⋯≥α[n], β[1]≥β[2]≥⋯≥β[n] are rearrangements of α and β in a descending order.” Here a≺b means that b strictly majorizes a. The imported moreMixed gives the prefix inequalities and equal totals, and desc gives the descending rearrangement. Natural orders are cast into the real carrier of these operations.

**Definition 1.4 (The multifactor quotient).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall k \in \mathbb{R},\; \forall a \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall b \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall x \in \mathbb{R},\; \operatorname{Q}\left(p, k, a, b, x\right) = \frac{\prod_{i: \operatorname{Fin}\left(n\right)} (\operatorname{polygamma}\left(p, k, a\left(i\right), x\right))}{\prod_{i: \operatorname{Fin}\left(n\right)} (\operatorname{polygamma}\left(p, k, b\left(i\right), x\right))}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.Q` (`✓ std3`).

*Citation.* Li Yin (2022). *Monotonic properties for ratio of the generalized (p,k)-polygamma functions*. DOI: [10.7153/jmi-2022-16-62](https://doi.org/10.7153/jmi-2022-16-62). URL: <https://files.ele-math.com/articles/jmi-16-62.pdf>.

*Commentary.*

Conjecture 4.1, p. 920: “For p,k>0 and every α₁,α₂,⋯αₙ,β₁,β₂,⋯βₙ∈ℕ such that (α₁,α₂,⋯,αₙ)≺(β₁,β₂,⋯,βₙ), the function Qα₁,α₂,⋯,αₙ;β₁,β₂,⋯,βₙ,p,k(x)=[ψₚ,ₖ⁽α₁⁾(x)⋯ψₚ,ₖ⁽αₙ⁾(x)]/[ψₚ,ₖ⁽β₁⁾(x)⋯ψₚ,ₖ⁽βₙ⁾(x)] is decreasing on (0,∞) onto the interval (((α₁−1)!⋯(αₙ−1)!)/((β₁−1)!⋯(βₙ−1)!),(α₁!⋯αₙ!)/(β₁!⋯βₙ!)).” Fin n indexes the n factors from zero; the source indexes them from one. Positive orders and positive x make every denominator factor nonzero.

**Definition 1.5 (Conjecture 4.1).**

$$\operatorname{claim}\iff (\forall p \in \mathbb{N},\; (0 < p) \Rightarrow (\forall k \in \mathbb{R},\; (0 < k) \Rightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\forall a \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall b \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; (\forall i \in \operatorname{Fin}\left(n\right),\; 0 < a\left(i\right)) \Rightarrow ((\forall i \in \operatorname{Fin}\left(n\right),\; 0 < b\left(i\right)) \Rightarrow ((\operatorname{StrictlyMajorized}\left(a, b\right)) \Rightarrow ((\operatorname{AntitoneOn}\left(\operatorname{Q}\left(p, k, a, b\right), \operatorname{Set.Ioi}\left(0\right)\right)) \land (\operatorname{Set.image}\left(\operatorname{Q}\left(p, k, a, b\right), \operatorname{Set.Ioi}\left(0\right)\right) = \operatorname{Set.Ioo}\left(\frac{\prod_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(a\left(i\right) - 1\right)\right): \mathbb{R}))}{\prod_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(b\left(i\right) - 1\right)\right): \mathbb{R}))}, \frac{\prod_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(a\left(i\right)\right)\right): \mathbb{R}))}{\prod_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(b\left(i\right)\right)\right): \mathbb{R}))}\right)))))))))$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.claim` (`✓ std3`).

*Citation.* Li Yin (2022). *Monotonic properties for ratio of the generalized (p,k)-polygamma functions*. DOI: [10.7153/jmi-2022-16-62](https://doi.org/10.7153/jmi-2022-16-62). URL: <https://files.ele-math.com/articles/jmi-16-62.pdf>.

*Commentary.*

Conjecture 4.1, p. 920: “For p,k>0 and every α₁,α₂,⋯αₙ,β₁,β₂,⋯βₙ∈ℕ such that (α₁,α₂,⋯,αₙ)≺(β₁,β₂,⋯,βₙ), the function Qα₁,α₂,⋯,αₙ;β₁,β₂,⋯,βₙ,p,k(x)=[ψₚ,ₖ⁽α₁⁾(x)⋯ψₚ,ₖ⁽αₙ⁾(x)]/[ψₚ,ₖ⁽β₁⁾(x)⋯ψₚ,ₖ⁽βₙ⁾(x)] is decreasing on (0,∞) onto the interval (((α₁−1)!⋯(αₙ−1)!)/((β₁−1)!⋯(βₙ−1)!),(α₁!⋯αₙ!)/(β₁!⋯βₙ!)).” The formula below retains both weak decrease and equality of the entire image with the open factorial interval. The parameters p and n and the orders are positive naturals; k is a positive real. The letters a and b encode α and β. Natural subtraction at order minus one is protected by positivity.

**Theorem 1.6 (Refutation of Conjecture 4.1).**

$$\neg (\forall p \in \mathbb{N},\; (0 < p) \Rightarrow (\forall k \in \mathbb{R},\; (0 < k) \Rightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\forall a \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall b \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; (\forall i \in \operatorname{Fin}\left(n\right),\; 0 < a\left(i\right)) \Rightarrow ((\forall i \in \operatorname{Fin}\left(n\right),\; 0 < b\left(i\right)) \Rightarrow ((\operatorname{StrictlyMajorized}\left(a, b\right)) \Rightarrow ((\operatorname{AntitoneOn}\left(\operatorname{Q}\left(p, k, a, b\right), \operatorname{Set.Ioi}\left(0\right)\right)) \land (\operatorname{Set.image}\left(\operatorname{Q}\left(p, k, a, b\right), \operatorname{Set.Ioi}\left(0\right)\right) = \operatorname{Set.Ioo}\left(\frac{\prod_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(a\left(i\right) - 1\right)\right): \mathbb{R}))}{\prod_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(b\left(i\right) - 1\right)\right): \mathbb{R}))}, \frac{\prod_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(a\left(i\right)\right)\right): \mathbb{R}))}{\prod_{i: \operatorname{Fin}\left(n\right)} ((\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(b\left(i\right)\right)\right): \mathbb{R}))}\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/yin-polygamma-majorization-refutation` (refuted) by `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yin-polygamma-majorization-refutation","declaration_gid":"D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Li Yin (2022). *Monotonic properties for ratio of the generalized (p,k)-polygamma functions*. DOI: [10.7153/jmi-2022-16-62](https://doi.org/10.7153/jmi-2022-16-62). URL: <https://files.ele-math.com/articles/jmi-16-62.pdf>.

*Commentary.*

For every p≥1, k>0, m≥2 and length l+2, take a constant tuple of order m and a second tuple with first two orders m−1,m+1 and l remaining orders m. The second tuple strictly majorizes the first. Cancelling nonzero common factors reduces Q to m/(m+1) times the neighboring-moment quotient. The Gram identity gives a strictly positive dispersion gap, so this quotient lies strictly between zero and m/(m+1) at every positive x. Both endpoint limits equal m/(m+1), excluding weak monotonicity in either direction. The final contradiction uses p=k=1, m=2 and l=1. This argument concerns finite truncations; it asserts no conclusion for ordinary untruncated polygamma functions.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.Q`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.StrictlyMajorized`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.claim`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.polygamma`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.psi`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.result`
- Dependency: [D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing](../../Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.md)
- Dependency: [D5/S3/QuantumBounds/LagrangeGramIdentity](../../QuantumBounds/LagrangeGramIdentity.md)
