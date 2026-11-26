# Two-insertion bound for the four-copy trace

## Abstract

Two-insertion bound for the four-copy trace

**Theorem 1.1 (Signed trace bound by the commutator energy).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/Tracial/CircleHessian.fourMarkTraceHessian_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/Tracial/CircleHessian.fourMarkTraceHessian_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

In a common eigenbasis for the drift and the Hermitian second factor, integrate the trace of two perturbation insertions against the independent and periodic arc counts. The resulting quadratic coefficient dominates the squared Frobenius norm of the commutator multiplied by the second factor. The bound permits signed eigenvalues and has no dependence on the dimension or spectral gaps.

**Theorem 1.2 (Comparison under a random arc mass).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/Tracial/CircleHessian.fourMarkTraceInsertionDefect_le_expected`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/Tracial/CircleHessian.fourMarkTraceInsertionDefect_le_expected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

A probability distribution of arc masses with a fixed mean only increases the two-insertion expectation. In the common eigenbasis the fourth power of the affine spectral interpolation is convex even for signed eigenvalues.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/Tracial/CircleHessian.fourMarkTraceHessian_lower`
- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/Tracial/CircleHessian.fourMarkTraceInsertionDefect_le_expected`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMV/Tracial/HingeMoments](HingeMoments.md)
