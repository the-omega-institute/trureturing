---
bibkey: nist2026lerch
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: Hurwitz Zeta Function
doi: null
url: https://dlmf.nist.gov/25.11.E18
claim: The derivative of the Hurwitz zeta function at zero equals log Gamma of its parameter minus one half of log two pi.
strata_touched:
  - D5/S3/Analytic/HolonomyDeterminant/ReflectedHurwitzDerivative
license: citation-only
triage: anchor
---

# Lerch's derivative formula

Equation (25.11.18) gives
`ζ′(0,a) = log Γ(a) − log(2π)/2`.
For a real parameter strictly between zero and one, the same identity at `1-a`
gives the reflected formula. Reflection on the additive circle sends the class
of `a` to the class of `1-a`.

The Lean proof uses regularized differences of Hurwitz and Riemann finite sums.
Their increments are interpolation remainders with a summable uniform bound.
The limit is identified by analytic continuation; convergence of its derivatives
and the Bohr-Mollerup limit for log Gamma determine the derivative at zero.
The constant is supplied by the Riemann zeta derivative at zero.

## Verified locator

- URL: https://dlmf.nist.gov/25.11.E18

The equation's TeX representation at https://dlmf.nist.gov/25.11.E18.tex
states the displayed identity with the derivative in the first zeta argument.
