# Signed Laplace moments

## Abstract

Derivatives and positive-part bounds for signed Laplace moments

The positive-part moment inequality has no integrability or measurability premise. If the signed real moment is not integrable, multiplying the complex integrand by a continuous unit-modulus phase shows that it too is not integrable. Both signed Bochner integrals then have the total value zero. The Laplace derivative and window applications establish genuine absolute integrability separately.

Let h be a measurable real function. Suppose its exponentially weighted integral on the nonnegative axis is absolutely convergent at every real parameter greater than a. The complex transform uses exp(-zu). The moment of order k inserts the factor u to the power k into this integral.

**Theorem 1.1 (Polynomial weights preserve interior exponential convergence).**

Lean statement: `D5/S3/Analytic/Laplace/SignedMoments.absolute_moment_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/SignedMoments.absolute_moment_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural k and real sigma greater than a, the function u to the power k times the absolute value of h(u), damped by exp(-sigma u), is integrable. The measure with density the absolute value of h converts this statement into the polynomial moment theorem for a moment-generating function.

**Theorem 1.2 (Absolute convergence of the complex moments).**

Lean statement: `D5/S3/Analytic/Laplace/SignedMoments.moment_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/SignedMoments.moment_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex z with real part greater than a, each complex moment is absolutely integrable. Its integrand norm is the corresponding absolute real moment at the real part of z.

**Theorem 1.3 (Differentiating a signed moment).**

Lean statement: `D5/S3/Analytic/Laplace/SignedMoments.moment_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/SignedMoments.moment_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of the moment of order k is minus the moment of order k+1. Choose a real damping parameter strictly between a and the real part of z. On the resulting complex neighborhood, the absolute moment at that parameter dominates the differentiated kernel. Dominated differentiation therefore applies without a sign restriction on h.

**Theorem 1.4 (All derivatives are actual signed moments).**

Lean statement: `D5/S3/Analytic/Laplace/SignedMoments.iteratedDeriv_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/SignedMoments.iteratedDeriv_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and every z with real part greater than a, the derivative of order k of the signed Laplace transform is (-1) to the power k times the moment of order k. The equality concerns the actual integral, and follows by induction using equality of germs throughout the open half-plane.

**Theorem 1.5 (The real center gives the signed real moment).**

Lean statement: `D5/S3/Analytic/Laplace/SignedMoments.alternating_derivative_real`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/SignedMoments.alternating_derivative_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a real center sigma greater than a, multiply the derivative of order k by (-1) to the power k and divide by k factorial. The real part is exactly the real signed moment of order k divided by k factorial. The two alternating signs cancel, and integration commutes with the real embedding.

**Theorem 1.6 (The one-sided bound for signed moments).**

Lean statement: `D5/S3/Analytic/Laplace/SignedMoments.moment_norm_add_real_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/SignedMoments.moment_norm_add_real_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a natural k and a complex z, with arbitrary real density h. The inequality uses total Bochner integrals and needs no premises. The norm of the complex moment, plus that real signed moment, is at most twice the moment with h replaced by max(h,0). The triangle inequality and the identity absolute(h)+h=2 max(h,0) give this estimate. No eventual sign or positivity assumption is imposed on h.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/SignedMoments.absolute_moment_integrable`
- Truth anchor: `D5/S3/Analytic/Laplace/SignedMoments.alternating_derivative_real`
- Truth anchor: `D5/S3/Analytic/Laplace/SignedMoments.iteratedDeriv_laplace`
- Truth anchor: `D5/S3/Analytic/Laplace/SignedMoments.moment_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/Laplace/SignedMoments.moment_integrable`
- Truth anchor: `D5/S3/Analytic/Laplace/SignedMoments.moment_norm_add_real_le`
- Dependency: [D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation](QuantitativeFejerBoundary/Continuation.md)
