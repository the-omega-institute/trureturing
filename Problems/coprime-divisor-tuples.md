---
slug: coprime-divisor-tuples
bibkey: wiseman2021a062319
doi: null
url: https://oeis.org/A062319
triage: theorem
motivation_gids:
  - D5/S3/Arith/CoprimeDivisorTuples.result
---

# Pairwise Coprime Ordered Tuples of Divisors

## Problem

OEIS A062319, "Number of divisors of n^n, or of A000312(n)", carries a comment
by Gus Wiseman dated May 02 2021 and still standing at revision #60 of
Aug 30 2026:

> Conjecture: The number of divisors of n^n equals the number of pairwise
> coprime ordered n-tuples of divisors of n. Confirmed up to n = 30.

The comment goes on to print the tuples counted for `n = 1` through `n = 5`.
Those lists fix two readings the words leave open: the value one may occur and
may repeat, so the constant tuple of ones counts, and the order of the
coordinates matters, so `(1,2)` and `(2,1)` count separately.

## Motivation

The frozen theorem `D5/S3/Arith/CoprimeDivisorTuples.result` settles the
comment in the affirmative for every `n ≥ 1`, and does so by way of a statement
in which the tuple length is a free parameter, so that the comment is the
diagonal case.

## Gap

Issue 9455 records the screen carried out before the work. A062319 appears
nowhere under `Problems/`, `D5/`, `Library/` or `docs/` in this repository
except in the triage record `Library/Words/oeis2026triage0910.md`, where it was
parked as note-only, not dropped, on the ground that the count sits close to
existing prime factorisation and divisor cardinality theorems and that the
wider literature on coprime tuples had not been checked. That check is what
this dossier closes.

The entry is absent from the 492-statement corpus of arXiv:2608.11941, from
every run of the `epoch-research/LeanOpenProblems-results` collection, and from
the Lean files of `google-deepmind/alphaproof-nexus-results`. Its two nearest
cross-references carry no proof: the unordered analogue A343654, "pairwise
coprime n-multisets of divisors of n", lists only further cross-references, and
the array A343656, of which this sequence is the diagonal, carries only the
divisor count formula. Searches of arXiv abstracts for pairwise coprime tuples
of divisors returned nothing. Citation indices and printed sources were not
exhaustively reachable, so this is a bounded negative finding.

## Route

Both sides equal `∏ p ∈ primeFactors n, (1 + n · m_p)`, where `m_p` is the
exponent of `p` in `n`.

The right side is immediate. The exponent of `p` in `n^n` is `n · m_p`, so the
divisor count of `n^n` is that product. The entry already records the same
product as a formula for its own terms, so the settlement rests on the tuple
side.

The tuple side factors over the primes of `n`. Pairwise coprimality says
exactly that for each prime `p` dividing `n`, at most one coordinate of the
tuple is divisible by `p`. So the exponent matrix of a tuple splits into one
column per prime, and each column is a vector of bounded entries that is zero
except in at most one place. A column is therefore either identically zero, one
possibility, or determined by a coordinate together with an exponent between
`1` and `m_p`, which is `n · m_p` possibilities. Multiplying over the primes
gives the product, with no appeal to multiplicativity as an external theorem.

The formal argument builds three bijections and composes them. A divisor of `n`
is identified with its bounded exponent vector; a pair of divisors is coprime
exactly when no prime has positive exponent in both; and a sparse column is
identified with an option type over the pairs consisting of a coordinate and a
positive exponent.

The tuple length must be a parameter independent of `n`. The one-parameter
form, in which the length is tied to the modulus, is not multiplicative in `n`,
so the induction that proves the product formula has to be carried out at fixed
length.

## Falsifier

A tuple that is pairwise coprime yet has two coordinates divisible by a common
prime of `n`, or a prime column with a second nonzero entry, would break the
splitting. A different reading of the entry, one that forbids repeated ones or
identifies a tuple with its reordering, would give a different left-hand count;
the worked lists on the entry exclude both readings, since `(1,1,1,1,1)` is
listed and `(1,2)` and `(2,1)` are listed separately.

## Evidence

Brute-force enumeration of the tuples for `n = 1..7` gives
`1, 3, 4, 9, 6, 49, 8`, agreeing term by term with the divisor counts of `n^n`,
with the product `∏ (1 + n · m_p)`, and with the entry's own data line. The
product formula agrees with the divisor count of `n^n` also at
`n = 8, 9, 10, 12, 16, 18, 24, 30, 36, 60`. The tuple side is exponential to
enumerate, so it was checked directly only to `n = 7`; the proof covers the
rest.

The mathematics is elementary. What the settlement records is that a named
published assertion had not been judged, not that the argument is deep.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9455
before the work. The admission basis is `open-problem-resolution`. The
computational use is `none`: no declaration is a bounded enumeration, a
checker, a numeric reduction or a certified instance, and the delivered
statement is universally quantified over all positive `n`.

## ASSUMED-UNVERIFIED

The literature screen is bounded. The entry was read in full at revision #60;
A343654, A343656, the arXiv corpus of 2608.11941, the
`epoch-research/LeanOpenProblems-results` runs and the
`google-deepmind/alphaproof-nexus-results` Lean files were checked; arXiv
abstract searches for pairwise coprime tuples of divisors were run. Citation
indices and printed sources were not exhaustively reachable, so no worldwide
priority claim is made.
