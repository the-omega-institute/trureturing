---
bibkey: ephremidze2010polynomial
authors: Lasha Ephremidze
year: 2010
title: An Elementary Proof of the Polynomial Matrix Spectral Factorization Theorem
doi: null
url: https://arxiv.org/pdf/1011.3777v1
claim: A matrix polynomial positive definite almost everywhere on the real line has a polynomial factor nonsingular in the open upper half-plane, unique up to a constant right unitary multiplier.
strata_touched:
  - D5/S3/Analytic/ClosedLowerHalfPlaneFactorContinuity
license: citation-only
triage: anchor
---

## Verified locator

Author version: https://arxiv.org/pdf/1011.3777v1, Theorem 2, page 2.

## Scalar correspondence

Theorem 2 on page 2 of the specified author version concerns real-line
polynomial matrix spectral factorization. The adjoint is coefficient
conjugation followed by transpose, with no reciprocal change of variable.
In dimension one, nonsingularity in the open upper half-plane permits real
zeros and says that all roots of the factor have nonpositive imaginary part.
For monic scalar factors, equality of leading coefficients removes the constant
unitary ambiguity. The conjugate product of a nonzero scalar polynomial is
positive on the real line except at its finitely many real zeros, so the
almost-everywhere positivity hypothesis applies to the supplied monic factors.

The uniqueness statement in ClosedLowerHalfPlaneFactorContinuity is this scalar
consequence, proved with polynomial root multiplicities. The Lean theorem
assumes the factors and does not prove the source's existence assertion.
The source theorem makes no assertion about continuity in parameters.
