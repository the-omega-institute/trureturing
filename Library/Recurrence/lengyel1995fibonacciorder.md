---
bibkey: lengyel1995fibonacciorder
authors: T. Lengyel
year: 1995
title: The Order of the Fibonacci and Lucas Numbers
doi: 10.1080/00150517.1995.12429139
url: https://fq.math.ca/Scanned/33-3/lengyel.pdf
claim: The p-adic order formulas for F_n and L_n include v_p(F_(nk))=v_p(F_n)+v_p(k) for p outside {2,5}, positive n and k, and rank(p) dividing n, with separate formulas for two and five.
strata_touched: []
license: citation-only
triage: anchor
---

# Fibonacci and Lucas p-adic orders

## Verified locator

T. Lengyel, *The Order of the Fibonacci and Lucas Numbers*, The Fibonacci
Quarterly 33(3) (1995), 234–239,
https://doi.org/10.1080/00150517.1995.12429139 .
Crossref identifies the author, title, volume, issue and pages. The journal
scan https://fq.math.ca/Scanned/33-3/lengyel.pdf gives the two- and five-adic
formulas in Section 2, Lemmas 1–2 (page 235), and the other prime valuations
in the unnumbered theorem of Section 3 (page 236).

## Claim and scope

Let alpha(p) be the least positive Fibonacci zero index and put
e(p)=v_p(F_alpha(p)). For p outside {2,5}, the theorem gives
v_p(F_n)=v_p(n)+e(p) if alpha(p) divides n, and zero otherwise.
Consequently, for positive n,k with alpha(p) dividing n,
v_p(F_(nk))=v_p(F_n)+v_p(k). The theorem also determines v_p(L_n).
The initial valuation e(p) is retained, not replaced by one.

Lemma 1 gives v_5(F_n)=v_5(n) and v_5(L_n)=0 for n>0. Lemma 2 gives
the separate two-adic cases: v_2(F_n)=0 when three does not divide n,
one when n is three modulo six, and v_2(n)+2 when six divides n;
v_2(L_n) is respectively zero, two and one in those three cases.

These formulas supply the classical square-divisibility threshold
attributed inline in FPD.1 of `Problems/wall-sun-sun-golden-unit-lift.md`.
The dossier provides a recurrence proof of that corollary. It does not
claim the valuation theory as new or infer the existence of a WSS prime.
