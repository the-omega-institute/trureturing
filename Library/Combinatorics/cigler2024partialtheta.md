---
bibkey: cigler2024partialtheta
authors: Johann Cigler
year: 2024
title: "Hankel determinants of backward shifts of the coefficients of a partial theta function"
doi: 10.48550/arXiv.2407.05768
url: https://arxiv.org/abs/2407.05768v2
claim: "Section 1 conjectures that the quotients r_{m,n}(q) of shifted Hankel determinants of the coefficients q^{binom(n,2)} are monic integer polynomials of degree mn(n+m+2)/2 with r_{m,n}(1) = 1 and r_{m,n}(0) = (-1)^{mn}."
strata_touched:
  - D5/S3/Combinatorics/PartialTheta/PartialThetaHankel
license: citation-only
triage: anchor
---

# Cigler, Hankel determinants of backward shifts of partial theta coefficients

The coefficients of the partial theta function Σ_{n≥0} q^{binom(n,2)} xⁿ are a(n, q) = q^{binom(n,2)}; one sets
a(n, q) = 0 for n < 0. The paper studies the Hankel determinants D_{−m,N}(q) = det(a(−m + i + j, q))_{0≤i,j<N} of the
backward shifts and defines r_{m,n}(q) by

D_{−m,n+m+1}(q) = (−1)^{binom(m+1,2)} r_{m,n}(q) q^{m binom(n,2)} D_{0,n+1}(q).

Section 1 conjectures that r_{m,n} is a monic polynomial with integer coefficients of degree mn(n + m + 2)/2 with
r_{m,n}(1) = 1 and r_{m,n}(0) = (−1)^{mn}; Theorems 1 and 2 prove the cases m = 1 and m = 2. The Appendix quotes a
conjecture of M. Schlosser on a weighted-partition interpretation; it is proved in Cigler, arXiv:2408.14094.

The module `D5/S3/Combinatorics/PartialTheta/PartialThetaHankel` proves the Section 1 conjecture for every m and n.

## Verified locator

DOI: 10.48550/arXiv.2407.05768

URL: https://arxiv.org/abs/2407.05768v2

- Locator: Section 1, equation (2) and the Conjecture immediately after it.
- Locator: Theorems 1 and 2, the cases m = 1 and m = 2.
- Locator: Appendix, the conjecture attributed to M. Schlosser.
