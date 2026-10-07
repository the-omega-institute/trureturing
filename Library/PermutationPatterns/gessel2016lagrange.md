---
bibkey: gessel2016lagrange
authors: Ira M. Gessel
year: 2016
title: "Lagrange Inversion"
doi: 10.48550/arXiv.1609.05988
url: https://arxiv.org/abs/1609.05988v1
claim: "Theorem 2.1.1 gives coefficient forms of Lagrange inversion; Section 2.3 applies them to the Catalan root f = C - 1 with R(t) = (1 + t)^2."
strata_touched:
  - D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo
  - D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge
license: citation-only
triage: anchor
---

# Gessel, Lagrange inversion

Gessel surveys the classical Lagrange inversion formula and several proofs. This note attributes
its coefficient identities; it makes no claim that these classical identities are new.

## Verified locator

DOI: 10.48550/arXiv.1609.05988

URL: https://arxiv.org/abs/1609.05988v1

Read the arXiv v1 HTML on 2026-10-06: <https://arxiv.org/html/1609.05988>.

- Theorem 2.1.1, equation (2.1.1): if f = xR(f), then for n ≠ 0,
  [x^n]φ(f) = (1/n)[t^(n−1)]φ′(t)R(t)^n. Taking φ(t) = t^k gives
  n[x^n]f^k = k[t^(n−k)]R(t)^n. The repository supplier retains rational
  formal power series, zero constant coefficient, and natural bounds 1 ≤ k ≤ n.
- Equation (2.1.2): [x^n]φ(f) = [t^n](1 − tR′(t)/R(t))φ(t)R(t)^n.
  Taking R(t) = (1 + t)^2 yields (1 − t)(1 + t)^(2n−1)φ(t).
  The bridge proves this specialization for arbitrary rational power series φ and natural n ≥ 1.
- Immediately before equation (2.1.7), Gessel sets g(t) = t/R(t) and explains that
  g(f) = x makes g the compositional inverse of f, when R has nonzero constant term.
  Here R(0) = 1 and g(t) = t/(1 + t)^2; the bridge retains and proves only ζ.subst q = X, the direction used to recover the original P13 counting series. The reverse companion is not retained.
- Section 2.3, equation (2.3.1): C = 1 + xC^2, followed by the substitution
  f = C − 1 and the equation f = x(1 + f)^2. The bridge constructs C from
  Mathlib’s PowerSeries.catalanSeries rather than assuming an analytic square-root expression.

## Repository lineage and scope

The generic proof is extracted from the existing proof of
NonnestingOneThreeTwoTwo.result, retained once in its original module as
lagrange_coefficient, and consumed by that result and by CatalanLagrangeBridge.
Mathlib’s RingTheory/PowerSeries/Catalan.lean (Weijie Jiang, 2025) supplies
catalanSeries, catalanSeries_constantCoeff and catalanSeries_sq_mul_X_add_one;
its substitution, inverse and order APIs supply the corresponding formal-series operations.
Elizalde and Luo’s separate elizalde2024pattern note remains the source of the
original 1322 counting problem, not the source of the classical generic inversion formula.
These classical identities supply the coefficient transform and lawful inverse direction.
The separate repository-derived `P13Enumeration.actual_A_eq_G` proves the actual matching-carrier
identification; `P13Enumeration.result` applies the transform to obtain the P13 all-size enumeration.
