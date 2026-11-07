---
bibkey: luschnytebni2022a355257
authors: Peter Luschny and Mélika Tebni
year: 2022
title: OEIS A355257, logarithmic coefficient array and congruence conjectures
doi: null
url: https://oeis.org/A355257
claim: The divisibility criterion for positive columns other than four and the prime quotient congruence for even rows of the logarithmic coefficient array.
strata_touched:
  - D5/S3/Arith/Congruence/TebniA355257Divisibility
  - D5/S3/Arith/Congruence/TebniA355257Quotient
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A355257

OEIS A355257, revision 37, NAME and COMMENTS, unpaginated.

## Source statements

> Array read by ascending antidiagonals. A(n, k) = k! * [x^k] log((1 - x) / (1 - 2*x)) / (1 - x)^n, for 0 <= k <= n.

> Conjecture: Let n >= 0, k >= 1 and k != 4. Then k divides A(n, k) if and only if k is not prime.

> Conjecture: For p prime and n even, (A(n, p) / (p - 1)) == 1 (mod p).

The quotient conjecture is attributed to Mélika Tebni. The coefficient expression
is interpreted over rational formal power series for all natural n and k.
The formal claims express integrality by an integer equal to the rational
coefficient, or to its rational quotient. Natural indices include zero.

## Mathematical scope

Coefficient convolution gives an integer finite sum. Modulo k its last term is
(k-1)!(2^k-1), independent of n. Wilson's theorem and factorial divisibility give
the divisibility classification. Modulo p-1 only the term with denominator p-1
can remain; the even-row hypothesis handles primes three and five. The residue
minus one modulo p then gives the quotient residue one.

The experiment is in the private repository
`the-omega-institute/trureturing-experiments`, directory
`docs/reports/oeis-a355257-a355407-a355414-log-egf-congruences/`, commit
`43e699d21346a1c6156fbac2901ce602af85ccd9`. Its `check.py` has SHA-256
`3b4ea949d0ef742d98627cd45c7a436d1721f7ad03eb1351f9455f0d9c0937c2`.
The recorded command `python3 check.py 30 200` exited zero with `RESULT PASS`.
These are the preregistration's experiment readings, not a new execution.

The literature screen read Fried's arXiv:2607.24832, which addresses the n=3
prime-residue case, and arXiv:2410.07237 and arXiv:2606.09913. The separate
A355259 polynomial-column conjecture remains outside these results.
Completeness of the literature screen is ASSUMED-UNVERIFIED.

OEIS material is cited with attribution; this note does not redistribute the
database or the experiment program.
