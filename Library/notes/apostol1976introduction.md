---
bibkey: apostol1976introduction
title: Introduction to Analytic Number Theory
doi: 10.1007/978-1-4757-5579-4
claim: Euler products, von Mangoldt weights, and the logarithmic derivative of the zeta function.
strata_touched:
  - D5/S3/Weil/EulerProduct
license: citation-only
triage: anchor
---

# Introduction to Analytic Number Theory

Tom M. Apostol develops finite and infinite Euler products, the von Mangoldt
function, and the logarithmic derivative of the Riemann zeta function in the
classical convergence half-plane. These results anchor the prime-power
coefficient and logarithmic-derivative declarations in
`D5/S3/Weil/EulerProduct`.

The book does not state the repository declarations verbatim. In particular,
Lean's field inverse is a total function with `0^-1 = 0`, so the formal finite
Euler theorem separates nonvanishing on the regular locus from the exact
denominator-zero lattice. That totalization qualification is repo-derived.
The formal statement also omits the source volume's empirical finite-window
certificate and does not claim a meromorphic pole order.

## Search log

- 2026-07-17: Queried NyxID/Tavily for `"finite Euler product" zero-free
  poles Riemann zeta DOI`. Results located standard Euler-product references
  and the Springer record for Apostol's book.
- 2026-07-17: Queried `"Introduction to Analytic Number Theory" Apostol DOI
  10.1007`. The publisher metadata verified the title and DOI
  `10.1007/978-1-4757-5579-4`, and its contents identify the chapters on
  Dirichlet series, Euler products, zeta, and L-functions.
- 2026-07-17: Queried `"von Mangoldt" "logarithmic derivative" Riemann zeta
  DOI`. Results restated the classical prime-power definition and the identity
  `-zeta'(s)/zeta(s) = sum Lambda(n)n^(-s)` for real part greater than one.
- 2026-07-17: Queried `"half-density" normalized Dirichlet series unitary
  critical line Riemann zeta DOI` and then `"scaling ledger" "half-density"
  zeta "unitary"`. No scholarly source matched the repository's exact
  ledger formulation, so `CriticalLine.unitarity_line_iff` remains
  `repo-derived`.
- 2026-07-17: The first three proxy calls sent JSON with the wrong transport
  shape and received HTTP 422, repeating a failure already recorded by the
  preceding batch. Reissuing raw JSON on stdin with
  `Content-Type: application/json` succeeded; no bibliographic conclusion was
  drawn from the failed calls.

## Verified locator

- DOI: https://doi.org/10.1007/978-1-4757-5579-4
