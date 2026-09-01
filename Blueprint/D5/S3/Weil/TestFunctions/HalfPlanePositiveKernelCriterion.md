# Half-Plane Positive Kernel Criterion

## Abstract

Finite Gram positivity packages the half-plane positive-kernel criterion for the Riemann hypothesis.

**Theorem 1.1 (Half-plane positive-kernel RH criterion).**

$$\operatorname{RiemannHypothesis}\left(\right) \Leftrightarrow \operatorname{IsPosDefKernel}\left(xiKernel\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/HalfPlanePositiveKernelCriterion.half_plane_positive_kernel_rh_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The point type abstracts the half-plane with real part greater than one half. Positive definiteness means that every finite sampled Gram matrix is positive semidefinite, including repeated points.

The xi-kernel equivalence is retained as an explicit source-criterion hypothesis because the pinned library does not supply the required Hadamard expansion. Independently, the Lean module proves diagonal reality and nonnegativity, conjugate symmetry, the two-point Cauchy-Schwarz bound, and both positive and negative kernel witnesses.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/HalfPlanePositiveKernelCriterion.half_plane_positive_kernel_rh_criterion`
