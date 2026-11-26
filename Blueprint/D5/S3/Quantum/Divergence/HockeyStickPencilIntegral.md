# The fixed-shift integral in the hockey-stick representation

## Abstract

The weighted negative inertia of a shifted finite Hermitian pencil is an exact spectral sum.

**Definition 1.1 (Pencil weight).**

Lean statement: `D5/S3/Quantum/Divergence/HockeyStickPencilIntegral.pencilWeight`

*Formalization.* `D5/S3/Quantum/Divergence/HockeyStickPencilIntegral.pencilWeight` (`✓ std3`).

*Citation.* Péter E. Frenkel (2023). *Integral formula for quantum relative entropy implies data processing inequality*. DOI: [10.22331/q-2023-09-07-1102](https://doi.org/10.22331/q-2023-09-07-1102). URL: <https://arxiv.org/abs/2208.12194>.

*Commentary.*

The weight at real t is the reciprocal of the product |t|(t-1)^2. Real inversion assigns zero at t=0 and t=1.

**Theorem 1.2 (The weighted negative inertia of the actual pencil).**

Lean statement: `D5/S3/Quantum/Divergence/HockeyStickPencilIntegral.integral_weighted_negIndex_shifted_pencil`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/HockeyStickPencilIntegral.integral_weighted_negIndex_shifted_pencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Péter E. Frenkel (2023). *Integral formula for quantum relative entropy implies data processing inequality*. DOI: [10.22331/q-2023-09-07-1102](https://doi.org/10.22331/q-2023-09-07-1102). URL: <https://arxiv.org/abs/2208.12194>.

*Acknowledgement.* Christoph Hirche and Marco Tomamichel (2024). *Quantum Rényi and f-divergences from integral representations*. DOI: [10.1007/s00220-024-05087-3](https://doi.org/10.1007/s00220-024-05087-3). URL: <https://arxiv.org/abs/2306.12343>.

*Acknowledgement.* Anna Jenčová (2024). *Recoverability of quantum channels via hypothesis testing*. DOI: [10.1007/s11005-024-01775-2](https://doi.org/10.1007/s11005-024-01775-2). URL: <https://arxiv.org/abs/2303.11707>.

*Acknowledgement.* Po-Chieh Liu, Christoph Hirche and Hao-Chung Cheng (2025). *Layer Cake Representations for Quantum Divergences*. URL: <https://arxiv.org/abs/2507.07065>.

*Acknowledgement.* Lukas Schmitt (2026). *Relative entropy representations via tracial joint spectral measures*. URL: <https://arxiv.org/abs/2609.12547>.

*Commentary.*

Let A and B be matrices on a finite complex coordinate space and let r be real with X=A+rI and Y=B+rI positive definite. The shifts imply that both A and B are Hermitian. Set R to the inverse of the positive square root of X. The theorem proves integrability on the real line of the pencil weight times the strict negative eigenvalue count of A+t(B-A)+rI. Its integral is the sum of log(1+λ)-λ/(1+λ) over the eigenvalues of R*(B-A)R, where R* is the conjugate transpose of R and equals R. Congruence reduces the count to the number of tests 1+tλ<0 that hold. Positive λ tests give a left tail and negative λ tests give a right tail. Each contribution is computed by the real improper fundamental theorem of calculus. A zero eigenvalue contributes zero.

Frenkel's Lemmas 4–5 and Theorem 6 give the shift and affine-pencil representation of relative entropy. Hirche and Tomamichel's Corollary 2.3 gives the two-profile form, and Jenčová's Corollary 1 gives the normalized forward finite-interval form. Liu, Hirche and Cheng's §4.1 gives an earlier operator layer-cake proof. Schmitt's Corollary 4.2 gives the unnormalized affine-pencil and forward-profile formulas.

**Theorem 1.3 (Integration over all positive shifts).**

Lean statement: `D5/S3/Quantum/Divergence/HockeyStickPencilIntegral.lintegral_weighted_negPart_pencil`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/HockeyStickPencilIntegral.lintegral_weighted_negPart_pencil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Péter E. Frenkel (2023). *Integral formula for quantum relative entropy implies data processing inequality*. DOI: [10.22331/q-2023-09-07-1102](https://doi.org/10.22331/q-2023-09-07-1102). URL: <https://arxiv.org/abs/2208.12194>.

*Acknowledgement.* Po-Chieh Liu, Christoph Hirche and Hao-Chung Cheng (2025). *Layer Cake Representations for Quantum Divergences*. URL: <https://arxiv.org/abs/2507.07065>.

*Acknowledgement.* Lukas Schmitt (2026). *Relative entropy representations via tracial joint spectral measures*. URL: <https://arxiv.org/abs/2609.12547>.

*Commentary.*

For finite positive semidefinite A and B, the nonnegative integral of the pencil weight times the negative-part trace equals the integral over positive r of the fixed-shift spectral sum. The finite layer-cake formula expresses the negative-part trace as an integral of strict negative inertia. Ordered eigenvalue continuity gives joint measurability, so Tonelli's theorem exchanges the pencil parameter and the positive shift.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/HockeyStickPencilIntegral.integral_weighted_negIndex_shifted_pencil`
- Truth anchor: `D5/S3/Quantum/Divergence/HockeyStickPencilIntegral.lintegral_weighted_negPart_pencil`
- Truth anchor: `D5/S3/Quantum/Divergence/HockeyStickPencilIntegral.pencilWeight`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound](../Matrix/LinGProperty/ArithmeticBound.md)
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../../SpectralTopology/HermitianEigenvaluePerturbation.md)
- Dependency: [D5/S3/Weil/Pick/DiagonalSignNegativeIndex](../../Weil/Pick/DiagonalSignNegativeIndex.md)
- Dependency: [D5/S3/Weil/ZetaLinear/FullRankInertiaPullback](../../Weil/ZetaLinear/FullRankInertiaPullback.md)
