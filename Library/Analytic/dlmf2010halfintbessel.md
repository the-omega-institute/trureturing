---
bibkey: dlmf2010halfintbessel
authors: NIST Digital Library of Mathematical Functions
year: 2010
title: "DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions"
doi: null
url: https://dlmf.nist.gov/10.17.E1
claim: "At order m+1/2 the Bessel expansion coefficients truncate and have the factorial normalization (m+k)!/(2^k k! (m-k)!) for 0 <= k <= m."
strata_touched:
  - D5/S3/Analytic/HalfIntegerBesselPolynomial
license: citation-only
triage: anchor
---

## Verified locator

[DLMF 10.17.1](https://dlmf.nist.gov/10.17.E1) gives the product with factors
$4\nu^2-(2j-1)^2$ for $1\le j\le k$ and denominator $k!8^k$.
At $\nu=m+1/2$, each factor is $4(m+1-j)(m+j)$. Multiplying these
factors gives the stated factorial formula for $k\le m$ and a zero
factor for $k>m$. The finite expansions in
[DLMF 10.49.8](https://dlmf.nist.gov/10.49.E8) and
[DLMF 10.49.12](https://dlmf.nist.gov/10.49.E12) use these coefficients
with the sign and reciprocal argument of the corresponding carrier.
