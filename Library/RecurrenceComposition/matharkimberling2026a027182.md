---
bibkey: matharkimberling2026a027182
authors: R. J. Mathar and Clark Kimberling
year: 2026
title: "OEIS A027182: self-convolution of the four-diamondized Pascal row"
doi: null
url: https://oeis.org/A027182
claim: "The self-convolution sequence of A027170 satisfies the six-term integer recurrence in the A027182 FORMULA field for n at least 6."
strata_touched:
  - D5/S1/Recurrence/MatharA027182SelfConvolution
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A027182

Underlying array: https://oeis.org/A027170

The source is unpaginated. The quoted entries are A027182 revision 8 and
A027170 revision 32. Neither has an arXiv identifier or a DOI.

## Source statement

A027170, definition:

> Triangular array T read by rows (4-diamondization of Pascal's triangle). Step 1: t(n,k) = C(n+2,k+1) + C(n+1,k) + C(n+1,k+1) + C(n,k). Step 2: T(n,k) = t(n,k) - t(0,0) + 1. Domain: 0 <= k <= n, n >= 0.

A027182, name and comment:

> a(n) = self-convolution of row n of array T given by A027170.

> Let g(x) = Sum_(k=0..n) A027170(n,k)*x^k be the generating function of row n, then a(n) = [x^n] g(x)^2. - R. J. Mathar, May 06 2026

A027182, FORMULA:

> Conjecture: D-finite with recurrence 2*(n+2)*a(n) +(-17*n-23)*a(n-1) +(47*n+36)*a(n-2) +2*(-22*n-17)*a(n-3) +4*(-n+20)*a(n-4) +8*(2*n-9)*a(n-5) +24*(12*n-47)=0. - R. J. Mathar, May 06 2026

The formal proposition asserts the recurrence at every natural index at
least 6, with integer coefficient arithmetic. Natural subtraction is used
in the row definition and sequence indices. The polynomial expression
also defines the natural extension a(0)=1. The source example prints
5*5+10*10+5*5=120; the defining expression instead evaluates to 150.

## Mathematical relation

Row symmetry identifies the central self-convolution with a square sum.
Vandermonde and the binomial row sums give a combination of three central
binomial coefficients, minus 72*2^n plus 16*n+40. A four-shift combination
of the central-binomial recurrence gives the six-term operator.

## Computed evidence

The exact checker is in `the-omega-institute/trureturing-experiments`,
commit `cf3aaa31442cac5cd2997b9c5577b98e339a310d`, directory
`docs/reports/mathar-a027182-recurrence/`. The `check.py` SHA-256 is
`ed87e906c89a49cda14ed1a5cfbd18654a26f99e85b08de1ecccf71d48b7c0c1`.
Running `python3 check.py` exits 0 with `ALL_CHECKS_OK`: it checks the
closed form for n=0..25, the recurrence for n=5..30, and an exact symbolic
operator identity. These finite checks do not prove the universal claim.

## Literature boundary

Issue #23023 records the source and literature screen. No published
settlement was found in that screen. Completeness and continued external
open status are ASSUMED-UNVERIFIED. Three identified Mathar works could
not be read in full; several search services returned rate limits or
access restrictions. Minimal annihilator order, parameterized
diamondization families and a formal D-finiteness API remain open here.
