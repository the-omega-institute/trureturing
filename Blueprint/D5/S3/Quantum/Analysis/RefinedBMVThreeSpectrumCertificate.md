# The refined BMV lower bounds for three spectral values in every degree

## Abstract

The refined BMV lower bounds for three spectral values in every degree

**Theorem 1.1 (The product lower bound in every positive degree).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate.three_spectrum_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate.three_spectrum_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite matrices A and B in any finite dimension, the normalized word trace with p copies of A and three of B bounds the trace of the cube of A raised to p/3 times B from below. The degree p is any positive integer and A has at most three distinct eigenvalues, with arbitrary multiplicities. The scalar discriminant in two logarithmic gaps is a finite exponential sum. The kernel checks its sparse integer coefficient table and the signs of all mixed initial values as polynomials in p minus one. A sequence of first-order equations propagates these signs to the entire nonnegative quadrant. The centered trace pairing then gives the matrix bound, with continuity covering zero roots.

**Theorem 1.2 (The exponential lower bound in every positive degree).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate.three_spectrum_exponential`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate.three_spectrum_exponential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For Hermitian matrices H and K, the normalized word trace of their exponentials bounds the trace of the exponential of pH plus 3K from below. The degree p is any positive integer and H has at most three distinct eigenvalues. Hägele's dyadic trace comparison takes the product bound to this limit.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate.three_spectrum_exponential`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate.three_spectrum_product`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumReduction](RefinedBMVThreeSpectrumReduction.md)
