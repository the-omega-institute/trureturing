# The compensated lower Poisson mode

## Abstract

A compensated lower Poisson mode is integrable and has an explicit hyperbolic cotangent integral.

**Theorem 1.1 (Whole-line lower boundary integral).**

Lean statement: `D5/S3/Analytic/PetzCothStripMode.integral_lowerMode`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzCothStripMode.integral_lowerMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real frequency omega, the lower Poisson weight pi/(cosh(2 pi s) - 1) multiplied by the cosine deficit 1 - cos(omega s) is Lebesgue integrable. Its integral is zero at frequency zero. At nonzero frequency, put x = omega/2. The integral is x coth(x) - 1.

Yang's width-one-half strip Poisson formula supplies the weight. On the positive ray it expands into exponential terms with rate and prefactor 2 pi n for n starting at one. The compensated Laplace integral of each term is omega squared divided by the sum of omega squared and the squared rate. Summability justifies termwise integration. Reflection doubles the positive-ray integral, which the frozen coth partial fraction evaluates at x = abs(omega)/2.

## References

- Truth anchor: `D5/S3/Analytic/PetzCothStripMode.integral_lowerMode`
- Dependency: [D5/S3/Analytic/CothBernoulliDegree/PartialFraction](CothBernoulliDegree/PartialFraction.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](../Weil/ZetaGamma/ArchimedeanJumpDecomposition.md)
