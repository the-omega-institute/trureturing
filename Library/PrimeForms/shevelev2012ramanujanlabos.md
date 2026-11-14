---
bibkey: shevelev2012ramanujanlabos
authors: Vladimir Shevelev
year: 2012
title: "Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html
claim: "Conjecture 40. (cf. Proposition 18). lim sup_{n→∞} (R_n − L_n) = ∞."
strata_touched:
  - D5/S3/Arith/Primes/ShevelevConjectureForty
license: citation-only
triage: anchor
---

# Ramanujan and Labos primes

V. Shevelev, *Ramanujan and Labos Primes, Their Generalizations, and
Classifications of Primes*, Journal of Integer Sequences 15 (2012), Article
12.5.4. The publisher's HTML page is the URL above. The full text is available
as [PDF](https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.pdf)
and [TeX](https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.tex).

## Locator

https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html
is the publisher's HTML landing page for Journal of Integer Sequences 15,
Article 12.5.4. In the linked journal full text, Conjecture 40 is the
same-index infinite-limsup assertion; Proposition 18 is the preceding
comparison with R indexed by n+1. Journal Definition 1 defines R_n as the
largest prime satisfying pi(R_n)-pi(R_n/2)=n and proves its equivalence to
the least positive integer g(n) such that every real x >= g(n) satisfies
pi(x)-pi(x/2) >= n. This encoding uses that equivalent threshold form,
which is Definition 1 in the latest arXiv:0909.0715 version. The Labos
minimum is journal Definition 3 and latest-arXiv Definition 2.

## Source statements

Conjecture 40 states:

> Conjecture 40. (cf. Proposition 18). lim sup_{n→∞} (R_n − L_n) = ∞.

Definition 1 first describes R_n as the largest prime with interval count n.
The paragraph immediately following it proves the equivalent characterization
as the smallest positive integer g(n) for which x >= g(n) implies
pi(x)-pi(x/2) >= n. This minimum-threshold form is the one encoded here.
The Labos minimum is journal Definition 3 (latest arXiv:0909.0715
Definition 2), with source label `d2`:
L_n is the smallest positive integer with pi(L_n)-pi(L_n/2)=n.
Both source definitions apply to n >= 1; the Lean definitions are total on
the naturals and the main result explicitly restricts its index to n >= 1.

Proposition 18 states limsup(R_(n+1)-L_n)=infinity. Conjecture 40 removes
the index shift. Conjecture 41 asks for infinitely many peculiar primes
and is outside the present conclusion.

The encoded minimum-threshold characterization quantifies over real x.
Prime counting at a real argument
means prime counting at its floor; positive thresholds make natural floor
sufficient. Natural subtraction is justified by monotonicity, not assumed.

## Reuse and scope

Repository searches found the frozen prime-number limits in
`D5/S3/Arith/Robin/EulerLayerRootCorrection.prime_number_limits`, derived
from `MediumPNT` and the Mathlib square-root bound for psi minus theta.
Their theta limit supplies the eventual dyadic count growth used here.
Mathlib supplies the prime-counting recurrence, finite prime sums,
Chinese remainder theorem and Dirichlet theorem. The window construction
and the same-index separation use these existing results.
Independent literature completeness and the present external status of the
conjecture are ASSUMED-UNVERIFIED. The source statements and their index
conventions are fixed by the publisher's full text. Only short attributed
quotations and mathematical descriptions are reproduced.
