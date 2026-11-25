# The refined BMV lower bounds with three copies of the second factor

## Abstract

The refined BMV lower bounds with three copies of the second factor

**Theorem 1.1 (Product trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/LargeDegree.product_bound_all`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/LargeDegree.product_bound_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For every natural number p at least three, the mean trace of the words with p copies of A and three of B is at least the trace of the cube of A^(p/3) B. The complex PSD factors may be singular and have arbitrary spectra in any finite dimension. Hägele's Lemma 3 and Sections 3 and 4 supply the composition average and cubic walk expansion. The degrees from three to ten use the proved finite cases. For larger degrees, the proof assembles the strict mixed derivative sign of the original logarithmic kernel from the left and right strips and the three central gap ranges. The two endpoint limits complete the rectangle inequalities for the finite interval Gram decomposition. Continuity of the unnormalized sample matrices covers zero centers. The centered walks and the Schur product theorem then give the product bound.

**Theorem 1.2 (Exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/LargeDegree.exponential_bound_all`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/LargeDegree.exponential_bound_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian H and K and every natural number p at least three, the word mean at exp H and exp K is at least the trace of exp(pH + 3K). The dyadic trace-power comparison in Hägele's Lemma 2 relates the product and exponential inequalities.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/LargeDegree.exponential_bound_all`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/LargeDegree.product_bound_all`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometricSign](PositiveCenter/LeftStripGeometricSign.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripWideSign](PositiveCenter/LeftStripWideSign.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleGapReplay](PositiveCenter/MiddleGapReplay.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedFourKernel](PositiveCenter/SeparatedFourKernel.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV43](../RefinedBMV43.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic](../RefinedBMVExtremeAnalytic.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterBoundaryBridge](../RefinedBMVPositiveCenterBoundaryBridge.md)
