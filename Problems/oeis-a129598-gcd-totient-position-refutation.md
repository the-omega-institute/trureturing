---
slug: oeis-a129598-gcd-totient-position-refutation
bibkey: karttunen2007a129598
doi: null
url: https://oeis.org/A129598
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KarttunenGcdTotientPositionRefutation
---

# Refutation of the A129598 differing-position characterization

## Problem

OEIS A129598, NAME (verbatim):

> a(n) = n * A111089(n).

Antti Karttunen's COMMENT of May 1, 2007 (verbatim):

> Conjecture: differs from A050399 at the positions given by A089966. E.g., a(15)=75, instead of A050399(15)=225, a(30)=150, instead of A050399(30)=450, a(33)=363, instead of A050399(33)=1089, a(45)=225, instead of A050399(45)=1225.

The NAME of A050399 states (verbatim):

> Least k such that n = A009195(k) (= gcd(phi(k), k)).

The NAME of A089966 states (verbatim):

> Numbers k such that omega(k) = gpf(k) mod lpf(k), where omega=A001221, gpf=A006530 and lpf=A020639.

For natural numbers, define `g(m) := gcd(m, phi(m))`. Let
`greatestPrimeFactor(n)` be the last element of the prime-factor list, with
default zero, and define `a(1):=2` and
`a(n):=n*greatestPrimeFactor(n)` otherwise. Define `b(n)` to be the least
positive `m` satisfying `g(m)=n` when such an `m` exists, and zero otherwise.
Finally, define `inA089966(n)` to mean `n=1`, or that `n` is positive and the
number of its distinct prime factors equals
`greatestPrimeFactor(n) mod minFac(n)`. The literal refuted statement is
`for every natural n, 1<n implies ((a(n) != b(n)) iff inA089966(n))`.

Karttunen's separate Conjecture 2, that `a(n)` divides A050399(n), is not
claimed or assessed. No exact value or minimality statement for `b(n)` is
claimed.

## Motivation

The comment identifies all positions at which A129598 differs from A050399
with A089966. A single differing position outside A089966 refutes this literal
universal characterization.

## Gap

Preregistration issue #7766 records searches dated September 14, 2026. OEIS
A129598 history revisions #1 through #17, together with the checked A050399
and A089966 histories, contain no settlement of Conjecture 1. A089966's
published data contains 15, 33, and 45 but not 30, so Karttunen's own listed
example at 30 is inconsistent with the referenced sequence data.

The checked arXiv and MathOverflow surfaces contain no settlement. These
bounded surfaces do not establish exhaustive literature coverage, historical
openness, or publication priority.

## Route

Take `n=60`. The A129598 value is `a(60)=60*5=300`, but
`g(300)=gcd(300,phi(300))=20`, so `a(60)` is not a preimage of 60 under `g`.
The witness 900 satisfies `g(900)=60`; hence the defining existence condition
for `b(60)` holds, and `Nat.find_spec` gives `g(b(60))=60`. It follows that
`a(60) != b(60)` without computing or bounding the least preimage itself.
However, 60 has three distinct prime factors while
`greatestPrimeFactor(60) mod minFac(60)=5 mod 2=1`, so 60 is not in A089966.
The biconditional at 60 therefore contradicts the universal claim.

## Falsifier

A proof of the literal universal `claim` would falsify this refutation. The
result instead proves that `a(60) != b(60)` and that 60 is not in A089966.

## Evidence

- Lean module:
  `D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.lean`.
- Main theorem: `result : Not claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The profiled Lean process took 9.10 seconds wall time and 47.8 milliseconds
  of cumulative type checking, with maximum resident set size
  1,711,767,552 bytes.
- The finite certificate proves `a(60)=300`, `g(300)=20`, `g(900)=60`, and
  that 60 is not in A089966. It uses `Nat.find_spec` only to establish that
  `b(60)` is a preimage of 60; it does not compute its value or prove
  minimality. No private helper declaration is present.

The orchestrator independently computed `a(60)=300`, `g(300)=20`,
`g(900)=60`, and that 60 is not in A089966. Its bounded scan below 1300 found
447 discrepancies and found 60 to be the least discrepancy outside A089966.

These bounded computations support the single instance used by `result`; they
do not assert a classification of all counterexamples, a global
least-counterexample theorem, or any value of `b(60)`.

## Triage

`theorem`. The finite certificate at 60 refutes Karttunen's literal
differing-position characterization. No publication-priority claim is made.

## ASSUMED-UNVERIFIED

Historical openness after the checked OEIS histories, arXiv, and MathOverflow
surfaces is `ASSUMED-UNVERIFIED`. The 447-discrepancy scan and its least
non-example observation are also `ASSUMED-UNVERIFIED` beyond the single
kernel-certified instance at 60.
