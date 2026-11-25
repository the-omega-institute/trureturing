# Signed moments on long upper windows

## Abstract

A one-sided window controls all complex Laplace moments at one common order

Let g be a measurable real function with absolute value at most M exp(2u) for nonnegative u. Fix a nonnegative exponent theta, a real constant C, and a width b greater than one. Suppose g(u) is at most C exp(theta u) on the interval from U to bU. The transform integrates g(u) exp(-zu) over the nonnegative axis.

**Theorem 1.1 (The global growth bound supplies absolute convergence).**

Lean statement: `D5/S3/Analytic/Laplace/SignedWindowMoments.growth_convergence`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/SignedWindowMoments.growth_convergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real sigma greater than two, the weighted integral of g(u) exp(-sigma u) is absolutely convergent. The product of the growth envelope and the damping factor is an integrable exponential with rate sigma minus two.

**Theorem 1.2 (The interior gamma mass and the two exterior tails).**

Lean statement: `D5/S3/Analytic/Laplace/SignedWindowMoments.moment_bound_on_window`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/SignedWindowMoments.moment_bound_on_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a shape h strictly between one and b, and a real sigma greater than theta. Require the two gamma tail rates to be nonnegative and sigma times (1-h/b) to exceed two. This last condition also implies sigma greater than two. For the order k equal to floor(sigma h U), the norm of the derivative of order k at any z with real part sigma, plus the real signed moment at sigma, divided by k factorial, is at most K times (sigma-theta) to the power minus k. Here K is twice the sum of absolute(C) divided by (sigma-theta) and M times (1/sigma+b/(h sigma)).

The norm of the complex moment plus the real signed moment is bounded by twice the positive-part moment. On the window, its density is bounded by the exponential upper envelope, whose complete gamma integral is explicit. Outside the window, the absolute growth envelope and the adjustable gamma estimate control both tails at the same order.

**Theorem 1.3 (A fixed center works for every sufficiently distant window).**

Lean statement: `D5/S3/Analytic/Laplace/SignedWindowMoments.long_window_moment_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/SignedWindowMoments.long_window_moment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed width b greater than one there are a real sigma greater than both two and theta and a nonnegative K with the following property. For every U at least one satisfying the stated window upper bound, set k to floor(sigma (1+b) U/2). Then k is at least U, and the preceding estimate holds at every complex center with real part sigma. The constants do not depend on U or on the imaginary part of the center. No exponential loss in U is needed for a pointwise window upper bound.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/SignedWindowMoments.growth_convergence`
- Truth anchor: `D5/S3/Analytic/Laplace/SignedWindowMoments.long_window_moment_bound`
- Truth anchor: `D5/S3/Analytic/Laplace/SignedWindowMoments.moment_bound_on_window`
- Dependency: [D5/S3/Analytic/Laplace/CriticalGammaWindow](CriticalGammaWindow.md)
- Dependency: [D5/S3/Analytic/Laplace/SignedMoments](SignedMoments.md)
