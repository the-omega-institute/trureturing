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
  - D5/S3/Analytic/HalfIntegerBessel
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

The spherical-to-ordinary conversions in
[DLMF 10.47.7](https://dlmf.nist.gov/10.47.E7) and
[DLMF 10.47.9](https://dlmf.nist.gov/10.47.E9) give the ordinary finite
carriers of order $m+1/2$ on $\Re z>0$. With $C=\sqrt{\pi/2}$ and
$L=C e^z P_m(-1/z)/\sqrt z$, the regular combination is
$\pi I=L-(-1)^m K$. The normalization and orientation of the ordinary
Wronskian agree with [DLMF 10.28.2](https://dlmf.nist.gov/10.28.E2).
The ordinary equation is [DLMF 10.25.1](https://dlmf.nist.gov/10.25.E1).
