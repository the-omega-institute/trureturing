---
bibkey: bala2026totientsquareperiod
authors: Peter Bala
year: 2026
title: "OEIS A281180 and its hyperbolic EGF family: totient-square periods"
doi: null
url: https://oeis.org/A281180
claim: "Conjecture: the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below."
strata_touched:
  - D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod
  - D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod
  - D5/S1/Recurrence/Periodic/BalaA281183TotientSquarePeriod
  - D5/S1/Recurrence/Periodic/BalaA281184TotientSquarePeriod
  - D5/S1/Recurrence/Periodic/BalaA281440TotientSquarePeriod
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A281180

The unpaginated OEIS A281180 Name and Comments, revision #81, state:

> a(n) = (2*n-1)! * [x^(2*n-1)] S(x), where S(x) = Integral (1 + S(x)^2)^2 dx.
>
> Conjecture: the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 18 2026
>

The offset is one. The formal primitive has constant coefficient zero.
The exponential coefficient of index m is m! times the ordinary coefficient.
The conjecture asserts a shift by phi(k)^2 for every positive modulus k; it
asserts neither a least period nor a sharp onset.

The associated entries A281181, A281183, A281184 and A281440 use even exponential
coefficients of cosh(H), its square, its cube, and cosh(H) with H'=cosh(H)^7,
respectively. Their complete source quotations accompany their own statements.
Literature completeness is ASSUMED-UNVERIFIED. The source has no arXiv identifier.

## OEIS A281181

Source: https://oeis.org/A281181

E.g.f. C(x) satisfies C(x) = cosh( Integral C(x)^3 dx ). More generally, we conjecture that the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 16 2026

## OEIS A281183

Source: https://oeis.org/A281183

E.g.f. C(x)^2 = cosh( Integral C(x)^3 dx )^2 where C(x) is described by A281181. Conjecture: the sequence {a(n)} taken modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 16 2026

## OEIS A281184

Source: https://oeis.org/A281184

E.g.f. C(x)^3 = d/dx log(C(x) + S(x)), where C(x) and S(x) are described by A281181 and A281180, respectively. Conjecture: the sequence {a(n)} taken modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 16 2026

## OEIS A281440

Source: https://oeis.org/A281440

E.g.f. C(x) satisfies: C(x) = cosh( Integral C(x)^7 dx ). Conjecture: the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 19 2026
