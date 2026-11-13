---
slug: oeis-a025527-kline-prime-minus-one-totient-quotient
bibkey: kline2017a025527
doi: null
url: https://oeis.org/A025527/internal
triage: theorem
motivation_gids:
  - D5/S3/Factorization/KlineFactorialLcmTotient.result
---

# Kline's A025527 prime-minus-one totient quotient conjecture

## Problem

OEIS A025527 revision 82, FORMULA (verbatim):

> Conjecture: a(A006093(n)) = phi(A000142(A006093(n))) / phi(A003418(A006093(n))), where phi is the Euler totient function. - _Fred Daniel Kline_, Jun 03 2017

For every integer j >= 1, put p = Nat.nth Nat.Prime (j.toNat - 1),
m = p - 1, L(m) = lcm(1,...,m), and independently a(m) = m!/L(m).
The assertion is a(m) = phi(m!)/phi(L(m)), with both quotients in the
rationals. This includes j = 1, p = 2, m = 1 and phi(1) = 1. There is no
assertion for zero or negative j and no added premise.

## Motivation

This is Fred Daniel Kline's explicit OEIS conjecture from 2017, still
displayed in A025527 revision 82. It is a Tier 1 named external conjecture;
its source label supplies no global priority certificate. The exact statement
is preregistered in [issue #28542](https://github.com/the-omega-institute/trureturing/issues/28542).

## Gap

The bounded source qualification inspected OEIS revisions 82 through 53 and
the cross references A006093, A000142 and A003418. Solus, *Simplices for
Numeral Systems*, arXiv:1706.00480v2, Remark 3.1, discusses an empirical
factorial/LCM geometric factor and supplies no exact totient quotient answer.
Inspected repository private and public factorial/LCM and totient results
concern different assertions. Pinned Mathlib supplies the prime-support and
totient-product tools. Applicable GitHub Lean queries were available with
incomplete_results=false; inspected excerpts supplied no whole answer. This
is not-found-in-searched-scope, not exhaustive literature absence.

The result has proof_shape: bind-only and admission_basis:
open-problem-resolution. It has no escape witness and no direct frozen D5
dependency. Its only public mathematical declarations are the independent
definition a and the exact result; no companion theorem is claimed.

## Route

For m = p - 1, m! and L(m) have the same prime factors: a prime divides m!
exactly when it is at most m, and the prime factors of L(m) are precisely
the primes at most m. Euler's product formula expresses phi(m!) and
phi(L(m)) as their arguments multiplied by the same rational prime-factor
product. Positivity of L(m) and phi(L(m)) permits cross multiplication,
giving the required quotient equality. The independent definition
a(m) = m!/L(m) is unchanged.

The reused Mathlib facts include Nat.primeFactors_lcmUpto,
Nat.Prime.dvd_factorial, Nat.totient_eq_mul_prod_factors,
Nat.lcmUpto_ne_zero, Nat.lcmUpto_pos and Nat.totient_pos.

## Falsifier

An integer j >= 1 for which these exact rational values differ would refute
the literal assertion. Finite agreement alone would not prove it.

## Evidence

The resolved declaration is
`D5/S3/Factorization/KlineFactorialLcmTotient.result`. Its independently
defined quotient is `D5/S3/Factorization/KlineFactorialLcmTotient.a`.
The retained Lean proofs have axiom closure
[propext, Classical.choice, Quot.sound], without sorryAx or an extra axiom.
The source-bound dependent-family registration has a source-equivalence
bridge and an explicitly unknown continuation; the latter supplies no claim
of undecidability or inexhaustibility.

The corresponding Scribe theorem carries OpenProblemResolutionClaim with
ResolutionKind.Proved for this dossier. Computational utility is none:
the result is an unbounded symbolic identity, not a finite enumeration or
a certified numerical instance.

## Triage

Proved: the complete quoted conjecture, for every positive integer prime
index including the first, by
`D5/S3/Factorization/KlineFactorialLcmTotient.result`.

### What the settlement shows

- Proved mechanism (the same GID): equal prime supports give the two
  totients the same rational Euler-product factor. Positive denominators
  then give the exact quotient identity. No asymptotic estimate or finite
  cutoff enters the result.
- Scope boundary: the proof uses no primality fact about p. An identity
  for all natural inputs is suggested by this mechanism, but is outside
  the registered statement and remains an unregistered extension; no
  additional formal result is asserted. There is no numerical bound whose
  sharpness is at issue.
- Source boundary: no further theorem depending on this conjecture was
  identified in the inspected source. No new sequence terms, asymptotic
  claims, or conclusions about Solus's geometric constructions follow as
  registered results here. Those neighbouring questions remain open in
  this delivery.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive absence of a prior answer remain
ASSUMED-UNVERIFIED. The bounded source qualification and direct proof do
not certify either. The scope of the literature qualification is exactly
the inspected sources described above.
