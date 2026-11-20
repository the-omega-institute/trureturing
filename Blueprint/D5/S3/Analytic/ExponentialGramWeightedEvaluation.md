# Sharp weighted evaluation of finite exponential sums

## Abstract

The squared norm of evaluation at zero on a finite span of distinct exponential modes has sharp constant h times the number of modes for the energy with weight exp(-hs).

**Theorem 1.1 (The least weighted evaluation constant).**

$$\operatorname{IsLeast}\left(A, h \operatorname{card}\left(iota\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExponentialGramWeightedEvaluation.weighted_evaluation_least_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let iota be a nonempty finite index type, let the real frequencies omega(i) be distinct, and let h be positive. For complex coefficients a, set f_a(s) to the sum of a(i) exp(i omega(i) s). The set A consists of the real constants C for which the squared norm of f_a(0) is at most C times the integral of exp(-hs) times the squared norm of f_a(s) over [0, infinity), for every a. The displayed value belongs to A and is at most every member of A.

Mathlib's complex Laplace integral identifies the energy with the Gram quadratic form. Zero energy forces the exponential sum to vanish on the positive real axis. Mathlib's analytic uniqueness theorem and FiniteVandermondeTomography.finite_moment_readout_injective then force every coefficient to vanish. For the positive definite Gram matrix G and diagonal differentiation matrix D, the matrix identity hG minus the all-ones outer product equals GD plus the adjoint of D times G. Multiplication by the inverse of G and cyclicity of trace give the inverse Gram readout h times card(iota). DetectorSensorDickeOptimality.psd_cauchy_schwarz gives the bound, and applying the inverse Gram matrix to the all-ones vector attains it with positive energy.

## References

- Truth anchor: `D5/S3/Analytic/ExponentialGramWeightedEvaluation.weighted_evaluation_least_constant`
- Dependency: [D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography](GoldenTomography/FiniteVandermondeTomography.md)
- Dependency: [D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality](../Quantum/Measurement/DetectorSensorDickeOptimality.md)
