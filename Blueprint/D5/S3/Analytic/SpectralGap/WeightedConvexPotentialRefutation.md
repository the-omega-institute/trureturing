# WeightedConvexPotentialRefutation

## Abstract

Weighted Dirichlet eigenvalues and a fixed affine spectral gap comparison.

**Definition 1.1 (fixedPotential).**

$$\forall (x: \mathbb{R}), fixedPotential x = (x / 100)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.fixedPotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The potential is the affine function with slope one over one hundred and zero intercept.

**Definition 1.2 (fixedWeight).**

$$\forall (x: \mathbb{R}), fixedWeight x = (1 + (x - Real . pi / 2) / 100)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.fixedWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The weight is affine with slope one over one hundred and equals one at the interval midpoint.

**Theorem 1.3 (result).**

$$\neg (\forall (M : WithTop \mathbb{R}) (Nlo Nhi : \mathbb{R}) (V w : \mathbb{R} \to \mathbb{R}) , (1 : WithTop \mathbb{R}) < M \to 0 < Nlo \to 0 < Nhi \to potentialClass M V \to weightClass Nlo Nhi w \to ((\exists e : \mathbb{N} \to \mathbb{R} , isSpectrum V w e) \land (\exists e0 : \mathbb{N} \to \mathbb{R} , isSpectrum (Function . const \mathbb{R} 0) w e0)) \land (\forall (e e0 : \mathbb{N} \to \mathbb{R}) , isSpectrum V w e \to isSpectrum (Function . const \mathbb{R} 0) w e0 \to gap e0 \leq gap e))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-ahrami2605gap` (refuted) by `D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-ahrami2605gap","declaration_gid":"D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Open Problem 3.3, page 10: “Let w be a positive concave weight on [0,π]. Does the constant potential minimzer the fundamental spectral gap over the class of convex potentials. Equivalently,” “Γ[V,w]≥Γ[0,w]” “for every convex potential V.” The index zero is λ₁ and index one is λ₂. Both spectra are asserted to exist; the comparison quantifies over their min-max values. If both specified min-max spectra exist, fixedPotential and fixedWeight force a negative gap difference. A uniform geometric coefficient estimate controls the shooting determinant, and zero separation identifies its first two min-max values.

## References

- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.fixedPotential`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.fixedWeight`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.result`
- Dependency: [D5/S3/Analytic/MomentOrthogonalPrimitiveGap](../MomentOrthogonalPrimitiveGap.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapDeterminant](WeightedGapDeterminant.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapMajorant](WeightedGapMajorant.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate](WeightedGapPolynomialCertificate.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapStateSeries](WeightedGapStateSeries.md)
- Dependency: [D5/S3/Analytic/SpectralGap/WeightedGapVolterra](WeightedGapVolterra.md)
