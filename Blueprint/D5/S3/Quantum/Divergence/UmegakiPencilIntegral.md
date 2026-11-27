# The finite Umegaki pencil integral

## Abstract

The weighted negative-part pencil integral gives the corrected finite Umegaki pairing.

**Theorem 1.1 (Frenkel’s formula for a positive definite reference).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiPencilIntegral.lintegral_weighted_negPart_pencil_eq_umegaki`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiPencilIntegral.lintegral_weighted_negPart_pencil_eq_umegaki` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Péter E. Frenkel (2023). *Integral formula for quantum relative entropy implies data processing inequality*. DOI: [10.22331/q-2023-09-07-1102](https://doi.org/10.22331/q-2023-09-07-1102). URL: <https://arxiv.org/abs/2208.12194>.

*Acknowledgement.* Christoph Hirche and Marco Tomamichel (2024). *Quantum Rényi and f-divergences from integral representations*. DOI: [10.1007/s00220-024-05087-3](https://doi.org/10.1007/s00220-024-05087-3). URL: <https://arxiv.org/abs/2306.12343>.

*Acknowledgement.* Anna Jenčová (2024). *Recoverability of quantum channels via hypothesis testing*. DOI: [10.1007/s11005-024-01775-2](https://doi.org/10.1007/s11005-024-01775-2). URL: <https://arxiv.org/abs/2303.11707>.

*Acknowledgement.* Po-Chieh Liu, Christoph Hirche and Hao-Chung Cheng (2025). *Layer Cake Representations for Quantum Divergences*. URL: <https://arxiv.org/abs/2507.07065>.

*Acknowledgement.* Lukas Schmitt (2026). *Relative entropy representations via tracial joint spectral measures*. URL: <https://arxiv.org/abs/2609.12547>.

*Commentary.*

Let A be positive semidefinite and B positive definite on a finite complex coordinate space, including the empty space. Integrate the trace of the negative part of A+t(B−A) over all real t with respect to Lebesgue measure. The weight is 1/(|t|(t−1)²), assigned zero at t=0 and t=1. The nonnegative integral is finite and equals the real trace of A(log A−log B) minus the real trace of A−B, embedded into the nonnegative extended reals.

In the original two eigenbases the squared overlaps sum to one along each row and column. For eigenvalues a≥0 and b>0, the primitive (a+r)log((a+r)/(b+r)) tends to a log a−a log b at zero, with a log a equal to zero when a=0. Bounds obtained from the logarithm inequality on the quotient and its reciprocal give the limit a−b at infinity. Integrating the nonnegative negative derivative over r>0 and summing with the overlaps yields the corrected trace pairing.

Congruence by the inverse square root of A+rI transforms B+rI into I+K. The determinant identity gives the difference of traces of logs, and trace cyclicity gives the inverse contribution. Functional calculus in K's eigenbasis identifies their sum with the integrand of HockeyStickPencilIntegral.lintegral_weighted_negPart_pencil.

The affine-pencil formula is Frenkel’s Theorem 6. Hirche and Tomamichel give the two-profile form in Corollary 2.3 and Eq. (2.22). Jenčová’s Corollary 1 gives the normalized forward finite-interval form, and Schmitt’s Corollary 4.2 treats the unnormalized forms. Liu, Hirche and Cheng give an operator layer-cake proof in §4.1. The identity supplies an analytic input to the separate Fibonacci curve argument.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiPencilIntegral.lintegral_weighted_negPart_pencil_eq_umegaki`
- Dependency: [D5/S3/Quantum/Divergence/HockeyStickPencilIntegral](HockeyStickPencilIntegral.md)
- Dependency: [D5/S3/Quantum/Divergence/SpectralCeilingRelativeEntropy](SpectralCeilingRelativeEntropy.md)
- Dependency: [D5/S3/Resource/LogDet/LogDetInformationSubmodularity](../../Resource/LogDet/LogDetInformationSubmodularity.md)
