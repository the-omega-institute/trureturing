# Comparison of the two unified imaginarity measures

## Abstract

Unified imaginarity minimized over real states is bounded by conjugate divergence.

**Definition 1.1 (Unified relative entropy).**

$$\forall (d: \mathbb{N}), (\forall (\alpha: \mathbb{R}), (\forall (\beta: \mathbb{R}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.unifiedDivergence}\left(\alpha, \beta, \rho, \sigma\right): \mathbb{R}) = \frac{((\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(((\rho)^{\alpha}) \cdot ((\sigma)^{(((1: \mathbb{R})) - (\alpha))})\right)\right))^{\beta}) - ((1: \mathbb{R}))}{((\alpha) - ((1: \mathbb{R}))) \cdot (\beta)})))))$$

*Formalization.* `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.unifiedDivergence` (`✓ std3`).

*Citation.* Chuanfa Wu; Zhaoqi Wu (2025). *Two imaginarity monotones induced by unified (α,β)-relative entropy*. DOI: [10.1088/1572-9494/adbdbd](https://doi.org/10.1088/1572-9494/adbdbd). URL: <https://arxiv.org/abs/2506.09799v1>.

*Commentary.*

For real parameters α and β and complex square matrices ρ and σ, take the real part of the trace of the product of their powers, raise that real number to β, subtract one, and divide by (α − 1)β. The matrix powers ρ ^ α and σ ^ (1 − α) use Mathlib's CFC.instPowReal, hence CFC.rpow from continuous functional calculus. These powers are not taken entry by entry. On positive semidefinite matrices they are spectral powers, including at zero eigenvalues. The outer real power is Real.rpow. Equation (7), TeX lines 164–166, gives this relative entropy on states in its parameter range. The displayed definition extends the expression to all real parameters and all complex square matrices; real division is zero when its denominator is zero.

**Definition 1.2 (Divergence from the conjugate state).**

$$\forall (d: \mathbb{N}), (\forall (\alpha: \mathbb{R}), (\forall (\beta: \mathbb{R}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.imaginarityH}\left(\alpha, \beta, \rho\right): \mathbb{R}) = \operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.unifiedDivergence}\left(\alpha, \beta, \rho, \operatorname{D5.S3.Quantum.Tomography.MUB.MUBCompletionRelativeGramEquivalence.entrywiseConj}\left(\rho\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.imaginarityH` (`✓ std3`).

*Citation.* Chuanfa Wu; Zhaoqi Wu (2025). *Two imaginarity monotones induced by unified (α,β)-relative entropy*. DOI: [10.1088/1572-9494/adbdbd](https://doi.org/10.1088/1572-9494/adbdbd). URL: <https://arxiv.org/abs/2506.09799v1>.

*Commentary.*

The first imaginarity measure compares ρ with its entrywise complex conjugate, as in equation (13), TeX lines 203–205. D5.S3.Quantum.Tomography.MUB.MUBCompletionRelativeGramEquivalence.entrywiseConj conjugates each matrix entry in the fixed coordinate basis. For a Hermitian matrix this conjugate equals the transpose.

**Definition 1.3 (Infimum over real states).**

$$\forall (d: \mathbb{N}), (\forall (\alpha: \mathbb{R}), (\forall (\beta: \mathbb{R}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.imaginarityE}\left(\alpha, \beta, \rho\right): \mathbb{R}) = \operatorname{sInf}\left(\{(x: \mathbb{R}) \mid \exists (\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\sigma\right)) \land ((\operatorname{D5.S3.Quantum.Tomography.MUB.MUBCompletionRelativeGramEquivalence.entrywiseConj}\left(\sigma\right) = \sigma) \land (x = \operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.unifiedDivergence}\left(\alpha, \beta, \rho, \sigma\right))))\}\right)))))$$

*Formalization.* `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.imaginarityE` (`✓ std3`).

*Citation.* Chuanfa Wu; Zhaoqi Wu (2025). *Two imaginarity monotones induced by unified (α,β)-relative entropy*. DOI: [10.1088/1572-9494/adbdbd](https://doi.org/10.1088/1572-9494/adbdbd). URL: <https://arxiv.org/abs/2506.09799v1>.

*Commentary.*

The second imaginarity measure is the real infimum of the divergence values obtained from states σ fixed by entrywise conjugation. D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity means positive semidefinite with complex trace equal to one. Thus the conjugation condition says that every entry of σ is real, as in Definition 1, TeX lines 119–126. Equation (20), lines 347–349, uses a minimum over these states; the displayed definition uses sInf, without asserting that the infimum is attained. The set of values is nonempty and bounded below under the hypotheses of the comparison theorem.

**Definition 1.4 (The comparison in every positive finite dimension).**

$$(\operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.claim}) \Leftrightarrow (\forall (d: \mathbb{N}), (((1: \mathbb{N}) \le d) \to (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \to (\forall (\alpha: \mathbb{R}), ((\alpha \in \operatorname{Set.Ioo}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \to (\forall (\beta: \mathbb{R}), ((\beta \in \operatorname{Set.Ioc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \to (\operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.imaginarityE}\left(\alpha, \beta, \rho\right) \le \operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.imaginarityH}\left(\alpha, \beta, \rho\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chuanfa Wu; Zhaoqi Wu (2025). *Two imaginarity monotones induced by unified (α,β)-relative entropy*. DOI: [10.1088/1572-9494/adbdbd](https://doi.org/10.1088/1572-9494/adbdbd). URL: <https://arxiv.org/abs/2506.09799v1>.

*Commentary.*

For every natural d at least one, every density matrix ρ, every α strictly between zero and one, and every β strictly positive and at most one, the infimum over real states is at most the divergence from the conjugate state. This is the all-dimension reading of the conjecture in TeX lines 573–579, with the second measure expressed as an infimum. Singular density matrices are included.

**Theorem 1.5 (The real part gives a stronger comparison).**

$$\forall (d: \mathbb{N}), (((1: \mathbb{N}) \le d) \to (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \to (\forall (\alpha: \mathbb{R}), ((\alpha \in \operatorname{Set.Ioo}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \to (\forall (\beta: \mathbb{R}), ((\beta \in \operatorname{Set.Ioc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \to (\operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.imaginarityE}\left(\alpha, \beta, \rho\right) \le \operatorname{D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.imaginarityH}\left(\alpha, \beta, \rho\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu-wu-2025-unified-imaginarity-monotone-comparison` (proved) by `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu-wu-2025-unified-imaginarity-monotone-comparison","declaration_gid":"D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chuanfa Wu; Zhaoqi Wu (2025). *Two imaginarity monotones induced by unified (α,β)-relative entropy*. DOI: [10.1088/1572-9494/adbdbd](https://doi.org/10.1088/1572-9494/adbdbd). URL: <https://arxiv.org/abs/2506.09799v1>.

*Commentary.*

First, the entrywise conjugate of ρ is a density matrix: Hermitian symmetry identifies it with the transpose, which preserves positive semidefiniteness and trace. Let τ = (1/2 : ℂ) • (ρ + entrywiseConj ρ). Adding the two positive semidefinite matrices and scaling by the nonnegative complex scalar gives positive semidefiniteness, and linearity of trace gives trace one. Conjugation interchanges the summands and fixes the scalar, so τ has real entries.

The real trace of the product of two positive semidefinite matrices is nonnegative. Since continuous functional calculus gives positive semidefinite powers, every overlap Re tr(ρ ^ α * σ ^ (1 − α)) is nonnegative. To bound this overlap above by one for density matrices, set A = ρ ^ α and B = σ ^ (1 − α). Their nonnegative eigenvalues satisfy ∑ᵢ λᵢ ^ (1/α) = 1 and ∑ⱼ μⱼ ^ (1/(1 − α)) = 1: spectral trace evaluation and composition of the positive powers reduce these sums to the traces of ρ and σ.

Choose the eigenvector unitaries of A and B and put W equal to the adjoint of the first times the second. The squared moduli of the entries of W form a doubly stochastic matrix. The real trace of AB is the sum of λᵢμⱼ weighted by these squared moduli. Weighted arithmetic–geometric mean gives λᵢμⱼ ≤ α λᵢ ^ (1/α) + (1 − α) μⱼ ^ (1/(1 − α)). Summing with the nonnegative weights and using both their row and column sums reduces the upper bound to α + (1 − α) = 1.

Next put q = Re tr(ρ ^ α * (entrywiseConj ρ) ^ (1 − α)) and r = Re tr(ρ ^ α * τ ^ (1 − α)). Operator concavity of the power with exponent 1 − α bounds τ ^ (1 − α) below by the average of ρ ^ (1 − α) and (entrywiseConj ρ) ^ (1 − α). The difference is positive semidefinite. Its product with ρ ^ α therefore has nonnegative real trace. The exponent addition law gives ρ ^ α * ρ ^ (1 − α) = ρ, including at zero eigenvalues, so trace linearity yields (1 + q)/2 ≤ r.

Scalar concavity of the real β power on the nonnegative reals gives (1 + q ^ β)/2 ≤ ((1 + q)/2) ^ β. Its monotonicity then gives (1 + q ^ β)/2 ≤ r ^ β. For any two density matrices the overlap lies between zero and one, so its β power is at most one. The divergence is consequently nonnegative, because both its numerator and its denominator are nonpositive.

The denominator (α − 1)β is strictly negative. Subtracting one from the midpoint power inequality and dividing reverses the inequality, giving unifiedDivergence α β ρ τ ≤ imaginarityH α β ρ / 2. All divergence values over real states are bounded below by zero, and τ supplies one such value. The infimum is therefore at most unifiedDivergence α β ρ τ. Finally imaginarityH α β ρ is nonnegative, by applying divergence nonnegativity to ρ and its conjugate. Combining these facts gives imaginarityE α β ρ ≤ unifiedDivergence α β ρ τ ≤ imaginarityH α β ρ / 2 ≤ imaginarityH α β ρ.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.claim`
- Truth anchor: `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.imaginarityE`
- Truth anchor: `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.imaginarityH`
- Truth anchor: `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.result`
- Truth anchor: `D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison.unifiedDivergence`
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence](../Tomography/MUB/MUBCompletionRelativeGramEquivalence.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../../Resource/LogDet/PathSpectralClassical.md)
