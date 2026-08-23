# The Positive-Density Logarithmic Path Identity

## Abstract

A positive-density logarithmic divergence equals its weighted affine-inverse path energy.

**Theorem 1.1 (The logarithmic divergence is an affine-inverse path integral).**

$$\forall rho \in \operatorname{PositiveDefiniteDensityMatrix}\left(\right),\; \forall sigma \in \operatorname{PositiveDefiniteDensityMatrix}\left(\right),\; \operatorname{belavkinStaszewskiDivergence}\left(rho, sigma\right) = \operatorname{rightLogarithmicPathEnergy}\left(rho, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MeanKernels/BelavkinStaszewskiPath.belavkin_staszewski_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho and sigma be finite square complex positive-definite matrices, each with trace one. Define their logarithmic divergence as the trace of rho times the continuous-functional-calculus logarithm of sqrt(rho) times inverse(sigma) times sqrt(rho). Put delta = rho - sigma and m(u) = (1-u) sigma + u rho. The theorem identifies that divergence with the integral from zero to one of (1-u) times the trace of delta times inverse(m(u)) times delta.

The proof applies mathlib's exact scalar complex-logarithm integral and moves it through continuous functional calculus using cfc_setIntegral. Positive definiteness supplies every inverse and makes the sandwiched matrix logarithm legitimate. The frozen affine matrix inversion theorem then changes the inverse weighted sum into sigma times inverse(m(u)) times rho. Trace cyclicity, rho = m(u) + (1-u) delta, and trace(delta) = 0 yield the stated weight without assuming that rho and sigma commute.

The hypotheses are satisfiable: taking rho = sigma to be any strictly positive trace-one diagonal matrix makes both sides zero. The theorem does not assume its logarithm representation or its target path identity; both are derived from positivity, trace normalization, library functional calculus, and finite-dimensional matrix algebra.

## References

- Truth anchor: `D5/S3/Divergence/MeanKernels/BelavkinStaszewskiPath.belavkin_staszewski_path`
- Dependency: [D5/S3/Quantum/MatrixInversion](../../Quantum/MatrixInversion.md)
