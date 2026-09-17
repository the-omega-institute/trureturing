---
slug: oeis-a049591-prime-gap-divisor-characterization-refutation
bibkey: laboselemer2002a049591
doi: null
url: https://oeis.org/A049591
triage: theorem
motivation_gids:
  - D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation
---

# Refutation of the A049591 divisor-count prime-gap characterization

## Problem

OEIS A049591, NAME (verbatim):

> Odd primes p such that p+2 is composite.

Benoit Cloitre's COMMENT of April 13, 2002 (verbatim):

> Sequence appears also to give all n > 1 such that there is no prime p satisfying the inequality n < p < n+tau(n)^2 where tau(n)=A000005(n).

For natural numbers, define
`Term(n) := Odd(n) and Prime(n) and not Prime(n+2)`, and define
`NoPrimeInGap(n) := for every natural p, Prime(p) implies not
(n < p and p < n + card(divisors(n))^2)`. The literal refuted statement is
`for every natural n, 1 < n implies (Term(n) iff NoPrimeInGap(n))`.

The NAME definition is not refuted. The Bernoulli, `f(2p)=p`, Ianakiev 2019
quotient, and Ordowski 2020 congruence comments are not claimed or assessed.

## Motivation

Cloitre's comment identifies the sequence with all integers satisfying a
divisor-count prime-gap condition. A single integer satisfying that condition
but not the sequence definition refutes the literal universal characterization.

## Gap

Preregistration issue #7698 records searches dated September 14, 2026. OEIS
history revisions #1 through #50 contain no settlement of the characterization.
The 2020 "my mistake" note concerns a different 2019 factorial-congruence
comment and does not settle Cloitre's 2002 characterization.

The arXiv search was rate-limited (`ASSUMED-UNVERIFIED`). Exact searches
returned 0 results on OpenAlex, 0 on MathOverflow, and 0 on Semantic Scholar.
GitHub exact-phrase search returned one OEIS mirror. These bounded surfaces do
not establish historical openness, exhaustive literature coverage, or
publication priority.

## Route

Take `n=529=23^2`. Its divisors are 1, 23, and 529, so the divisor count is
three and the upper endpoint is `529+3^2=538`. Every integer from 530 through
537 is composite, so the open interval `(529,538)` contains no prime and
`NoPrimeInGap(529)` holds. But 529 is not prime, so `Term(529)` is false.
The biconditional at 529 therefore contradicts the universal claim.

## Falsifier

A proof of the literal universal `claim` would falsify this refutation. The
result instead supplies `NoPrimeInGap(529)` together with `not Term(529)`.

## Evidence

- Lean module:
  `D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.lean`.
- Main theorem: `result : Not claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The profiled Lean process took 3.25 seconds wall time and 137 milliseconds of
  cumulative type checking, with maximum resident set size 1,636,220,928 bytes.
- The finite certificate proves that 529 has divisor-count square 9, checks
  each possible prime in the open interval by cases, and checks that 529 is not
  prime. No private helper declaration is present.

The orchestrator's bounded scan of `[2,3000)` found 47 failures and found 529
to be the least. It independently computed the divisor set `{1,23,529}` and
the composite factorizations
`530=2*265`, `531=3*177`, `532=4*133`, `533=13*41`, `534=2*267`,
`535=5*107`, `536=8*67`, and `537=3*179`.

These bounded computations support the single instance used by `result`; they
do not assert a classification of all counterexamples or a global
least-counterexample theorem.

## Triage

`theorem`. The finite certificate at 529 refutes the literal universal
characterization. No publication-priority claim is made.

## ASSUMED-UNVERIFIED

The arXiv result is unverified because the search surface was rate-limited.
The bounded scan beyond the single certified instance, and historical openness
after the checked OEIS, OpenAlex, MathOverflow, Semantic Scholar, and GitHub
surfaces, are `ASSUMED-UNVERIFIED`.
