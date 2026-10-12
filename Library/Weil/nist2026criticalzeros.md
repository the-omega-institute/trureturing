---
bibkey: nist2026criticalzeros
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: "DLMF 25.10(i) and 27.4: critical-line zeros and the von Mangoldt Dirichlet series"
doi: null
url: https://dlmf.nist.gov/25.10.i
claim: The source records infinitely many critical-line zeros and the classical von Mangoldt series for the logarithmic derivative of zeta. Neither fact supplies a signed lower comparison for the theta operator.
strata_touched: []
license: citation-only
triage: anchor
---

# Critical-line infinitude and the complete prime-power series

The inspected [DLMF 25.10(i)](https://dlmf.nist.gov/25.10.i) states
that the real $Z(t)$ changes sign infinitely often, hence
$\zeta(1/2+it)$ has infinitely many real ordinates. Conjugation symmetry,
and isolated zeros give infinitely many distinct positive
ordinates. The section cites Titchmarsh, second edition, Section 4.17.
This classical infinitude is reused without a proportion estimate or
new zero computation.

[DLMF 27.4.12](https://dlmf.nist.gov/27.4.E12) gives
$\sum_{n\ge1}\Lambda(n)n^{-z}=-\zeta'(z)/\zeta(z)$.
The absolutely convergent Dirichlet-series domain is $\Re z>1$;
$\Lambda(n)\le\log n$ also directly bounds its absolute convergence
there. The inspected TeX encoding is [27.4.E12.tex](https://dlmf.nist.gov/27.4.E12.tex).
Every prime power is included, not just the primary primes.

The inspected DLMF release is 1.2.8, released 15 September 2026.
These are source statements, without independent proof reproduction or
Lean certification. Their [full-prime source-range application](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/critical-prime-source-range.md)
concerns a precise stronger factorization requirement, not RH or the
sign of the original arithmetic form.
