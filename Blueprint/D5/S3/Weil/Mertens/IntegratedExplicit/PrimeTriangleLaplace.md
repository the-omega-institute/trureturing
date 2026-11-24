# The Laplace transform of the prime triangle

## Abstract

The centered triangular Mangoldt sum retains the pole at each zeta zero in the critical strip.

**Theorem 1.1 (Absolute convergence and nonzero residues).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLaplace.hingeTransform_integral_and_zero_residues`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLaplace.hingeTransform_integral_and_zero_residues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In logarithmic coordinates, the centered Mangoldt triangle is the combination U(4 exp t) − 3U(2 exp t) + 2U(exp t). Its Laplace integral converges absolutely for Re(s) > 1. A shift by h multiplies the transform with its initial interval removed by exp(sh). Summing with coefficients 1, −3, and 2 gives (2^s − 1)(2^s − 2) times the original transform, minus an entire correction.

For a zero ρ with 0 < Re(ρ) < 1, the magnitude of 2^ρ lies strictly between 1 and 2. The multiplier therefore preserves the pole, giving residue (2^ρ − 1)(2^ρ − 2) times the multiplicity divided by ρ(1 − ρ).

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLaplace.hingeTransform_integral_and_zero_residues`
- Dependency: [D5/S3/Analytic/Laplace/EulerPoleObstruction](../../../Analytic/Laplace/EulerPoleObstruction.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent](CompleteMangoldtLaurent.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeQuarterTriangle](PrimeQuarterTriangle.md)
