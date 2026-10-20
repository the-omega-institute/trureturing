# SecondDifference

## Abstract

Positive definite functions and their integral representations.

**Theorem 1.1 (Translation differences).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.difference`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complex positive definite function and any real step h, the centered expression 2 f(t) minus f(t+h) minus f(t-h) is positive definite. A doubled finite family and the coefficient map with blocks I and minus I give the Gram congruence.

**Theorem 1.2 (Negative curvature).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.neg_second_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.neg_second_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real twice continuously differentiable positive definite function, the negative second derivative is positive definite. The centered differences divided by the squared step converge pointwise by two applications of the derivative quotient limit.

**Theorem 1.3 (Quadratic deficit integral).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.Q_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.Q_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an even twice continuously differentiable real function g, its deficit divided by t squared, with value minus one half of its second derivative at zero, equals the integral from zero to one of (1-u) times the negative second derivative at ut. The fundamental theorem applied to (1-u)t g prime(ut) plus g(ut) gives the identity.

**Theorem 1.4 (Positive quadratic deficit).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.Q_positiveDefinite`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.Q_positiveDefinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If g is even, twice continuously differentiable and positive definite, then its continuously extended quadratic deficit is positive definite. Negative curvature, arbitrary real dilation and the nonnegative weighted integral give the result.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.Q_integral`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.Q_positiveDefinite`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.difference`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.neg_second_deriv`
- Dependency: [D5/S3/Analytic/Fourier/PositiveDefinite/Closure](Closure.md)
