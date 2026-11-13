---
bibkey: hanna2021a350410family
authors: Paul D. Hanna
year: 2021
title: "OEIS A350410, A350411 and A350412: square-exponent factorial integrality"
doi: null
url: https://oeis.org/A350410
claim: "This sequence is conjectured to consist entirely of integers."
strata_touched:
  - D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality
license: citation-only
triage: anchor
---

## Verified locator

https://oeis.org/A350410

The other two source entries are https://oeis.org/A350411 and
https://oeis.org/A350412. The locators are the NAME, COMMENTS and EXAMPLE
fields of OEIS revisions 5, 5 and 9 respectively; web entries have no page
numbers. There is no associated arXiv identifier or identified journal paper.

## Source statements

%N A350410 G.f. A(x) = Sum_{n>=0} a(n)*x^n satisfies: 0 = [x^n] Sum_{m=0..n} A(x)^(m^2) / m!, for n > 1.

%C A350410 This sequence is conjectured to consist entirely of integers.

%e A350410 G.f.: A(x) = -1 + x + 3*x^2 + 12*x^3 + 116*x^4 - 534*x^5 - 19083*x^6 + 4653416*x^7 + 8687989872*x^8 - 128647855586426*x^9 + ...

%N A350411 G.f. A(x) = Sum_{n>=0} a(n)*x^n satisfies: 0 = [x^n] Sum_{m=0..n+1} A(x)^(m^2) / m!, for n > 1.

%C A350411 This sequence is conjectured to consist entirely of integers.

%e A350411 G.f.: A(x) = -1 + x + 6*x^2 + 76*x^3 + 74*x^4 + 26058*x^5 - 7794632*x^6 - 14388774920*x^7 + 213380711849598*x^8 + 28487519401892735386*x^9 + ...

%N A350412 G.f. A(x) = Sum_{n>=1} a(n)*x^n satisfies: 0 = [x^n] Sum_{m=0..2*n} (A(x) - 1)^(m^2) / m!, for n > 1, with A(0) = 0.

%C A350412 This sequence is conjectured to consist entirely of integers.

%e A350412 G.f.: A(x) = x + 12*x^2 + 830*x^3 + 1867901*x^4 + 251714851830*x^5 + 3696867014099083814*x^6 + 8468768030682252554158546818*x^7 + ...

The first two series have constant coefficient -1 and coefficient of x equal
to 1. The third has constant coefficient 0 and coefficient of x equal to 1.
All series are formal over the rationals. The finite sum includes both m=0
and its stated upper endpoint, and the equations hold in every degree n>=2.
Integer coefficients mean that each rational coefficient is the image of
an integer. The public claim expands this condition; the proofs use the
existing IntegralSeries predicate of HannaLogarithmicPowerClosure.

## Mathematical mechanism

At a series with constant coefficient -1, changing its degree-n coefficient
changes the square-power sum by that change times
(-1)^(M-1)/(M-1)!. This nonzero slope yields uniqueness. Multiplication by
(M-1)! clears all but the last summand's factorial denominator. Formal
differentiation shows that this last numerator is divisible by M when
M=n, n+1 or 2n. The resulting integer coefficient operator contracts
prefix agreement, so its integer fixed point supplies existence. Adding
one translates the third series to its source normalization.

## Finite computation

The exact-arithmetic checker is in the private repository
https://github.com/the-omega-institute/trureturing-experiments at commit
3e1d776b280735532b3ec74064a3400a04dcdfad, path
`docs/reports/hanna350410-square-exponent-integrality/check.py`, SHA-256
`2ae06627f32d7a1b359dfd49d927c62feb31de9ad056d20cd19a40cbfb5cd8a8`.
Issue https://github.com/the-omega-institute/trureturing/issues/27303 records
exit 0 and ALL_CHECKS_OK. The finite coefficient and divisibility checks
through n=13 support source fidelity; they do not prove the universal claim.

## Literature boundary

The literature screen in issue 27303 found no target-specific settlement
in the inspected sources. The related Heninger--Rains--Sloane root-integrality
paper concerns different Hanna sequences and fixed-root criteria.
OpenAlex and Semantic Scholar were rate-limited, and unrestricted discovery
was incomplete. Literature completeness is ASSUMED-UNVERIFIED; no originality
claim follows from these bounded searches.
