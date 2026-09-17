---
slug: oeis-a231329-price-nineteen-four-prime-exponent
bibkey: price2013a231329
doi: null
url: https://oeis.org/A231329
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/PricePrimeQuotientExponent.prime_quotient_exponent_is_prime
  - D5/S3/Arith/Congruence/PricePrimeQuotientExponent.result_a231329
---

# Price's A231329 prime-exponent conjecture

## Problem

OEIS A231329, NAME (`%N`, verbatim):

> Numbers n such that (19^n + 4^n)/23 is prime.

Robert Price's COMMENT (`%C`, verbatim):

> Conjecture: All terms are prime.

The literal proved statement is

`forall k : Nat, 23 | 19^k + 4^k -> Prime((19^k + 4^k)/23) -> Prime(k)`.

The divisibility hypothesis is explicit because the OEIS expression denotes an
exact integer quotient, while natural-number division would otherwise truncate.

Not claimed here are the A228558 comment `a(9) > 10^5`, the A231329 comment
`a(5) > 10^5`, infinitude of either sequence, primality of any particular term,
or the classical general factorization fact as a new result. That fact is the
same background argument as `2^n-1 prime -> n prime`.

## Motivation

The entry defines its sequence by prime values of an exponential quotient and
asks whether every exponent in that sequence is prime. The theorem proves this
for every natural exponent satisfying the exact divisibility and primality
hypotheses, through a general result that also applies to A228558.

## Gap

The following literature checks were recorded on 2026-09-15:

- Query: `OEIS A228558 full entry and revisions #1-#10`
  Outcome: The conjecture remains in the published entry. Revision #4 discussion records Price saying he had a partial proof, but the history contains no proof link or published settlement.
- Query: `OEIS A231329 full entry and revisions #1-#7`
  Outcome: The conjecture remains in the published entry. Revision #3 corrected an initial copy of A228558 to bases 19 and 4 with denominator 23; no revision supplies a proof.
- Query: `OpenAlex exact searches for A228558 and A231329`
  Outcome: HTTP 200; meta.count=0 for each exact identifier.
- Query: `Crossref exact searches for A228558 and A231329`
  Outcome: HTTP 200; total-results=0 for each exact identifier.
- Query: `OpenAlex search for "(a^n+b^n)/(a+b)" prime exponent and for Robert Price OEIS prime sequence`
  Outcome: The formula query returned 589 broad matches; the inspected top 10 were unrelated. The Robert Price/OEIS query returned meta.count=0.
- Query: `Mersenne prime exponent must be prime proof factorization`
  Outcome: MathWorld's Mersenne Prime entry states that a prime 2^n-1 requires n prime and gives the binomial factorization argument; it cites Hardy-Wright, An Introduction to the Theory of Numbers, 5th ed., pp. 14-16. This establishes the route as classical, not these OEIS settlements.
- Query: `Crossref title search: Aurifeuillian cyclotomic factorization`
  Outcome: Returned literature including Granville, Aurifeuillian factorization (Math. Comp. 2005, DOI 10.1090/S0025-5718-05-01766-7) and Allombert, Practical Aurifeuillian factorization (2009, DOI 10.5802/jtnb.641); no returned record identified either OEIS entry.
- Query: `OEIS exact expression searches for (17^n+4^n)/21 and (19^n+4^n)/23 plus Robert Price user page`
  Outcome: Each expression search returned only its corresponding entry; the user page supplies biography/contact information and no publication settling the claims.
- Query: `Internet Archive advanced search: A228558 OR A231329`
  Outcome: HTTP 200; numFound=0.
- Query: `arXiv API: A228558 OR A231329 and general prime-exponent shape`
  Outcome: HTTP 429; not verified on arXiv in this attempt.
- Query: `Semantic Scholar: A228558 A231329 and general prime-exponent shape`
  Outcome: HTTP 429; not verified on Semantic Scholar in this attempt.
- Query: `Google Books and Google Search exact identifiers/general Mersenne shape`
  Outcome: Google Books returned HTTP 429 daily quota exhaustion; Google Search returned an unusual-traffic CAPTCHA; not counted as zero-hit searches.

The general factorization route is classical. No published source settling
A228558 or A231329 specifically was found in the verified sources, so status
is not already-known. No exhaustive literature or priority claim is made.

## Route

First, under positivity and coprimality, `x+y` divides `x^k+y^k` exactly when
`k` is odd: the forward direction excludes even `k`, and
`Odd.nat_add_dvd_pow_add_pow` supplies the reverse direction.

Second, `k=1` makes `(x^k+y^k)/(x+y)=1`, which is not prime.

Third, if odd `k` is composite, write `k=d*m` with a proper divisor. The pinned
Mathlib ingredient `Odd.nat_add_dvd_pow_add_pow` gives the nested divisibilities.
The quotient-factor construction places `x^d+y^d` strictly between `x+y` and
`x^k+y^k`, so the two induced quotient factors are nonunits whose product is
the allegedly prime quotient. This contradiction forces `k` to be prime and
is the escape witness.

## Falsifier

A natural `k` for which 23 divides `19^k+4^k`, the exact quotient is prime,
and `k` is not prime would contradict `result_a231329`.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/PricePrimeQuotientExponent.lean`.
- `prime_quotient_exponent_is_prime`, `result_a228558`, and `result_a231329`
  each have std3 axiom closure `[propext, Classical.choice, Quot.sound]`.
- Kernel profile: wall time 3.42 seconds, type checking 53.5 milliseconds, and
  maximum resident set size 1,564,950,528 bytes.
- Deleting any one of the five direct imports makes the module fail to compile
  with exit 1; restoring all five gives a zero-exit serial build.
- For `k<400`, the exponents producing prime exact quotients are
  `7, 11, 211`, all prime.
- The bounded scan carries no proof of the universal statement.

## Triage

`theorem`. Price's A231329 comment is proved for every natural exponent under
the exact divisibility and quotient-primality hypotheses; the resolution is
`proved`, not `refuted`.

## ASSUMED-UNVERIFIED

Literature completeness outside the verified OEIS, OpenAlex, Crossref,
MathWorld, Internet Archive, and inspected search surfaces is unverified.
arXiv, Semantic Scholar, Google Books, and Google Search were not verified in
this attempt because of HTTP 429 responses or a CAPTCHA. The bounded scan is
independent exact-integer evidence but does not establish the theorem.
