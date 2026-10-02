---
bibkey: brandenhuh2020lorentzian
authors: Petter Brändén, June Huh
year: 2020
title: Lorentzian polynomials
doi: 10.4007/annals.2020.192.3.4
url: https://arxiv.org/abs/1902.03719v8
claim: Reciprocal-factorial generating polynomials of M-convex supports are Lorentzian, with positive-orthant root concavity and Hessian signature restrictions.
strata_touched:
  - D5/S3/Resource/SimplexCoverageHessian
  - D5/S3/Resource/SimplexCoveragePolynomial
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Combinatorics/brandenhuh2020lorentzian -->
# Lorentzian polynomials

The journal article is in *Annals of Mathematics* 192, issue 3, pages 821–891.
The source version used for the concavity-transfer route is arXiv:1902.03719v8.

## Mathematical interfaces

Section 2.2 gives the exchange condition for M-convex supports. Theorem 3.10,
implication (7) to (4), concerns normalized generating polynomials with
reciprocal-factorial coefficients. Theorem 2.30 and Proposition 2.33 supply
the positive-orthant log/root-concavity context. Polynomial support conditions,
nonzero evaluation, homogeneity, and degree hypotheses must be verified by a
consumer; a support-indicator polynomial is not the same normalized polynomial.

## Formal reuse boundary

The matrix component in `D5/S3/Resource/SimplexCoverageHessian` uses
Mathlib's finite real Hermitian eigenbasis and a maximum-ratio argument. It
does not import a formal Lorentzian theorem, establish the represented-span
polynomial induction, or settle a simplex optimizer conjecture. The citation
is published mathematical context, not kernel evidence or an independent
open-problem result.

`D5/S3/Resource/SimplexCoveragePolynomial` supplies the actual represented
coefficients and contractions, degree-two Hessian classification and reverse
inequality, positive-evaluation rank criterion, derivative-positive support
connectivity and rank/span zero obstructions. The higher-degree normalized
Hessian induction and the analytic and sampling bridges remain open.
