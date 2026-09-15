---
slug: oeis-a023887-yanev-sigma-radical-identity
bibkey: yanev2017a023887
doi: null
url: https://oeis.org/A023887
triage: theorem
motivation_gids:
  - D5/S3/Arith/YanevSigmaRadicalIdentity
---

# Yanev's general sigma-radical identity

## Problem

OEIS A023887, NAME (`%N`, verbatim):

> a(n) = sigma_n(n): sum of n-th powers of divisors of n.

Velin Yanev's FORMULA conjecture (`%F`, verbatim):

> Conjecture: sigma_m(n) = sigma(n^m * rad(n)^(m-1))/sigma(rad(n)^(m-1)) for n > 0 and m > 0, where sigma = A000203 and rad = A007947. - _Velin Yanev_, Aug 24 2017

AUTHOR (`%A`, verbatim):

> _Olivier Gérard_

The exact formal statement, with all variables natural, is
`forall n m, 0 < n -> 0 < m ->
sigma m n * sigma 1 (primeRadical n ^ (m - 1)) =
sigma 1 (n ^ m * primeRadical n ^ (m - 1))`, where
`D5/S1/Deficit/AlmostAdditivity.primeRadical n = ∏ p ∈ n.primeFactors, p`
is the frozen natural radical (A007947).
Both sides are positive under these hypotheses. The denominator is also
positive, so this multiplied-out form is equivalent to the quoted identity,
including its exact natural-number quotient. Subtraction in `m - 1` is
natural subtraction; the positive-`m` hypothesis makes it the usual predecessor.

## Motivation

The identity expresses a divisor sum of any positive exponent using only
ordinary divisor sums and the distinct prime factors of the input. It settles
the general-`m` assertion, extending the previously proved `m = 2` case.
The question and quantifiers were pre-registered in issue #7927 before the
probe, under the external named open-problem route.

## Gap

The repository's frozen `D5/S1/Deficit/AlmostAdditivity.primeRadical` (the same product of distinct prime factors) is reused; no statement of this conjecture exists in the repository.

The orchestrator's readings on 2026-09-15 were:

- OEIS A023887 still labels the `%F` line "Conjecture", with no settlement line.
- Sela Fried, "Proofs of some conjectures of Yanev" (2025, OEIS
  `a006519.pdf`), Theorem 3 proves the `m = 2` case on A001157 only.
- The arXiv API returned HTTP 429/503 at query time; arXiv was not searched.
- OpenAlex returned 14 unrelated hits concerning plant-biology grant numbers.
- MathOverflow returned one unrelated thread, 512305.
- GitHub code search returned only OEIS mirrors; formal-conjectures returned
  zero matches; repository prior-art search for `A023887` returned zero hits.

These are attributed external-source readings.
They do not establish exhaustive literature coverage or a priority claim.

## Route

1. Use Mathlib's prime-power and coprime induction principle.
2. On a prime power, apply the existing sigma and radical formulas. Three
   geometric-sum multiplication identities and positive cancellation give
   the required equality.
3. Extend through coprime multiplication using radical multiplicativity,
   coprimality of divisors and powers, and sigma multiplicativity.

The proof is `bind-only`: the needed facts come from pinned Mathlib and
normalization. There is no escape witness and no separate private theorem.
The admission basis is `open-problem-resolution`, pre-registered in #7927;
the public surface consists of one `result`, reusing the frozen `primeRadical`.
The utility classification is `none`: this is an unbounded symbolic identity,
not finite enumeration, a checker, numerical reduction, or a certified instance.

## Falsifier

Any positive natural pair `(n,m)` for which the displayed two sides differ
would refute the asserted identity. Agreement on finitely many pairs cannot
establish its universal quantifiers. The denominator is positive for every
pair in the stated domain, so division by zero is not a boundary case there.

## Evidence

- Module: `D5/S3/Arith/YanevSigmaRadicalIdentity.lean`.
- The theorem's axiom closure is `[propext, Classical.choice, Quot.sound]`.
- The orchestrator checked `1 <= n <= 300`, `1 <= m <= 4`, with zero exceptions.
- The probe reported zero exceptions for `1 <= n <= 400`, `1 <= m <= 5`.

## Triage

`theorem`; resolution `proved` for the general-`m` identity under `n > 0` and
`m > 0`. This is the mathematical resolution; repository freezing and
admission are not asserted by this dossier.

## ASSUMED-UNVERIFIED

The source quotations, pre-registration #7927, Fried theorem locator and
scope, and external search and numeric readings are attributed evidence;
independent verification is absent. arXiv was not searched because of the
reported API errors.
Historical openness beyond the checked sources remains unverified; no
exhaustive literature or priority claim is made.
