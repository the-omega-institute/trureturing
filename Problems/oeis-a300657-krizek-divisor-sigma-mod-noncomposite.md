---
slug: oeis-a300657-krizek-divisor-sigma-mod-noncomposite
bibkey: krizek2018a300657
doi: null
url: https://oeis.org/A300657
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite.result
---

# Krizek's A300657 noncomposite characterization

## Problem

OEIS A300657 defines

```text
a(n) = Sum_{d|n} sigma(d) mod d.
```

Its Comment line states verbatim:

> a(n) >= A054024(n). Conjecture: a(n) = A054024(n) only for the noncomposite numbers A008578.

The entry's Author line states verbatim:

> _Jaroslav Krizek_, Mar 10 2018

Here `A054024(n) = sigma(n) mod n`, and A008578 consists of one and the
primes. With

```text
a300657(n) = Sum_{d|n} (sigma(d) mod d),
```

the proved equivalence, with all quantifiers explicit, is: for every natural
number `n`, if `1 <= n`, then

```text
a300657(n) = sigma(n) mod n if and only if n = 1 or n is prime.
```

## Motivation

The conjecture asks for an exact characterization, rather than a one-sided
bound or a verification over a finite range. The theorem identifies every
natural index in the source's stated noncomposite class.

## Gap

The OEIS A300657 entry was read in full and still labels the characterization
as a conjecture. A MathDB search returned 0 hits. The repository search before
this addition returned no hit for `A300657`. These are bounded search results,
not an exhaustive claim that no independent proof exists.

## Route

For `n = 1` and for prime `n`, the divisor set evaluates directly and the
equality follows. Conversely, suppose `n >= 2` is composite and let `p` be
its least prime factor. Then `p` is a proper divisor of `n`, while
`sigma(p) mod p = 1`. Splitting the divisor sum at `n`, the asserted equality
would force the sum over all proper divisors to be zero. Nonnegativity would
then force its `p` term to be zero, contradicting the preceding value one.

## Falsifier

A natural `n >= 1` for which the displayed equality and the condition
`n = 1 or Prime(n)` have different truth values would refute the theorem.
Changing the divisor convention, the sigma function, or the natural-number
remainder changes the claim.

## Evidence

The source statement and definitions are recorded in
`Library/ArithSums/krizek2018a300657.md`. The frozen theorem is
`D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite.result`, with declaration
statement ID
`sha256:ec34455025c7da17b9598d70580779fac5ae4368e58a2dd453d57f1f4e5529d9`.
Its axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`.
The module freeze has no prerequisite frozen project nodes; the proof uses
only pinned Mathlib facts.

## Triage

First tier: an explicitly labelled conjecture in an OEIS entry,
preregistered in issue #8386. Resolution: `proved`.

| Declaration | proof_shape | computational_content.kind | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none | open-problem-resolution |

After unfolding the local definition, the proof consists of instantiating
pinned divisor and sigma lemmas, splitting a finite sum, choosing the least
prime factor, and arithmetic normalization. It therefore has no escape
witness. The external conjecture is admitted under
`open-problem-resolution`, not `escape-witness`. The uniform symbolic theorem
is not bounded enumeration, checker infrastructure, numeric reduction, or a
certified finite instance, so `utility: none` applies.

## ASSUMED-UNVERIFIED

The bounded literature checks do not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof. The Lean kernel does not
authenticate the external OEIS page or its revision history.
