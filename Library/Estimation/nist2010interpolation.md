---
bibkey: nist2010interpolation
authors: Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors
year: 2010
title: "NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation"
doi: null
url: https://dlmf.nist.gov/3.3
claim: "Classical interpolation, divided differences and equally spaced nodes underlie the derivative and binomial formulas for finite forward differences."
strata_touched: []
license: citation-only
triage: anchor
---

# Classical finite-difference background

The NIST Digital Library of Mathematical Functions, Section 3.3, treats
interpolation, divided differences and equally spaced nodes. For a real
function with the requisite differentiability on the entire closed node
interval, the repeated mean-value argument relates its order-R forward
difference to the order-R derivative at a point of that same interval.
The explicit binomial representation gives the sum of absolute coefficients
as 2^R. These are classical tools, as are affine annihilation and homogeneity
of a power under a positive change of scale.

`NonintegerForwardDifferenceSignal` uses these tools on the positive half-line.
Its nonvanishing statement assumes that the exponent differs from every
natural number; it also allows negative exponents. The exact target signal
at step rho/sqrt(n), with its coefficient and n^(-beta/2) dependence, is a
repository application of these classical identities. This note does not
attribute a sequential sampling lower bound to the DLMF.

## Verified locator

URL: https://dlmf.nist.gov/3.3.
The page identifies Section 3.3, *Interpolation*, in Chapter 3,
*Numerical Methods*, and includes divided differences and equally spaced nodes.
