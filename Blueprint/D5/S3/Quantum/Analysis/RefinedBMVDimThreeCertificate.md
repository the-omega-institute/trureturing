# The ordered scalar certificate for the refined BMV bounds

## Abstract

The ordered scalar certificate for the refined BMV bounds

**Theorem 1.1 (Nonnegativity of the quartic in ordered scalar deficits).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate.criterion_nonneg_ordered`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate.criterion_nonneg_ordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

Writing the three ordered cube roots as a common base and two successive nonnegative increments yields a polynomial with nonnegative integer coefficients. Lean checks their signs for word counts five, six, and seven by packing the coefficients into an integer and testing one bit per coefficient. A coefficient bound prevents carries from changing the signs.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate.criterion_nonneg_ordered`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVDimThreePackedCheck](RefinedBMVDimThreePackedCheck.md)
