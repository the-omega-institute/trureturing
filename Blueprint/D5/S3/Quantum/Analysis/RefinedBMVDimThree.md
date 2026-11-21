# The refined BMV lower bounds in dimension three

## Abstract

The refined BMV lower bounds in dimension three

**Theorem 1.1 (The trace-power comparison for five, six, or seven first factors).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVDimThree.product_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVDimThree.product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite complex matrices of size three, the trace of the cube of the product using the first factor's spectral power p/3 is bounded by the mean of all words with p first factors and three second factors. The ordered eigenvalue certificate and the single triangle pairing cover repeated and zero eigenvalues.

**Theorem 1.2 (The exponential comparison for five, six, or seven first factors).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVDimThree.exponential_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVDimThree.exponential_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For every complex Hermitian pair of size three, apply the product comparison to the exponentials of the first matrix divided by three and the second matrix. The dyadic trace-power comparison gives the lower bound for p equal to five, six, or seven. Hägele names the five-and-three question in Section 7 of arXiv:2611.00129v1.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVDimThree.exponential_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVDimThree.product_bound`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV43](RefinedBMV43.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate](RefinedBMVDimThreeCertificate.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVDimThreePairing](RefinedBMVDimThreePairing.md)
