---
bibkey: dlmf2010hermitecoefficients
authors: NIST Digital Library of Mathematical Functions
year: 2010
title: "DLMF 18.5.13, explicit representation of Hermite polynomials"
doi: null
url: https://dlmf.nist.gov/18.5.E13
claim: "The physicists Hermite polynomial has the finite factorial coefficient expansion in equation 18.5.13."
strata_touched:
  - D5/S3/Analytic/Polynomial/HermiteSignedMode
license: citation-only
triage: anchor
---

## Verified locator

Source: https://dlmf.nist.gov/18.5.E13.tex, equation 18.5.13.

$$
H_n(x)=n!\sum_{k=0}^{\lfloor n/2\rfloor}
\frac{(-1)^k(2x)^{n-2k}}{k!(n-2k)!}.
$$

The formal polynomial distributes n! into this finite sum and expands the power
of 2 in each monomial coefficient over the rationals. The coefficient selector
is therefore for physicists H_n. Pinned Mathlib Polynomial.hermite is the
probabilists polynomial and is not used as a substitute for this normalization.
