# The grouped trace lower bound for four and three copies

## Abstract

The grouped trace lower bound for four and three copies

**Theorem 1.1 (Grouped trace comparison).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/GroupedFourThree.grouped43_all`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/GroupedFourThree.grouped43_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For positive semidefinite complex matrices R and C of any common finite size, the mean of the real parts of the 35 word traces with three copies of R and four of C is at least the real part of the trace of R² C² R C². After diagonalizing C, a cyclic identity expresses the difference through kernels indexed by a spectral value of C. Each kernel is a sum of a rank-one kernel and a weighted Cauchy kernel. The Schur product theorem gives positivity, including at repeated and zero spectral values.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/GroupedFourThree.grouped43_all`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV43](../RefinedBMV43.md)
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV43Kernel](../RefinedBMV43Kernel.md)
