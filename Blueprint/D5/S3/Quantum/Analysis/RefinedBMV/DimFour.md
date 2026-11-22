# The refined BMV lower bounds in dimension four

## Abstract

The refined BMV lower bounds in dimension four

**Theorem 1.1 (The cube-root trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/DimFour.cubeRoot_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/DimFour.cubeRoot_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite complex matrices X and B of size four, the mean with p copies of X cubed and three copies of B dominates the trace of the cube of X to the power p times B. The comparison holds for p equal to five, six, or seven and uses all four spectral coordinates of X.

**Theorem 1.2 (The spectral-power trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/DimFour.product_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/DimFour.product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite complex matrices A and B of size four, take X to be the positive semidefinite cube root of A. The word mean dominates the trace of the cube of the product of the spectral power A to the exponent p/3 and B. The spectral power is defined also at zero eigenvalues.

**Theorem 1.3 (The exponential trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/DimFour.exponential_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/DimFour.exponential_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For every complex Hermitian pair of size four, apply the cube-root comparison to the exponential of H/3 and the exponential of K. The exact dyadic trace-power comparison bounds the trace of the exponential of p H plus 3 K by this word mean.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/DimFour.cubeRoot_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/DimFour.exponential_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/DimFour.product_bound`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV/DimFourScalar](DimFourScalar.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV/DimFourWalk](DimFourWalk.md)
