# First order gap

## Abstract

A strict radial gap for every finite positive p below q.

**Theorem 1.1 (Strict separation of evaluation and radial norm).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/FirstOrderGap.exists_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/FirstOrderGap.exists_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of finite real exponents with 0<p<q and every alpha>0, there is a real t strictly between zero and one for which the radial mixed norm power is strictly smaller than the normalized evaluation power. The parameter t is the square of the affine power-family parameter.

Write beta=alpha q and r=q/p. Monotone substitution u=1-rho squared evaluates the integrals of rho times (1-rho squared) to beta-1 and to beta. Their difference gives the second radial moment. The substitution also establishes interval integrability when the weight diverges at the outer endpoint.

Convexity of the real power with r>1 gives (1+t rho squared) to r at most 1+rho squared times ((1+t) to r minus 1). Integration bounds the radial quantity by U(t)=1+((1+t) to r minus 1)/(beta+1). Both U and the normalized evaluation equal one at zero. Their derivatives are respectively r/(beta+1) and r/(1+alpha p). Since q>p, the evaluation derivative is strictly larger. The right-hand slope limit therefore gives strict separation for a sufficiently small positive t.

## References

- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/FirstOrderGap.exists_gap`
- Dependency: [D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Radial](Radial.md)
