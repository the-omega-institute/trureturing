---
slug: oeis-a177680-twin-prime-average-multiple-of-five
bibkey: gerasimov2010a177680
doi: null
url: https://oeis.org/A177680
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive
---

# The A177680 twin-prime averages modulo five

## Problem

OEIS A177680, NAME (`%N`, verbatim):

> Numbers n such that 6n and 12n are both the average of twin prime pairs.

COMMENT (`%C`, verbatim; Harvey P. Dale, Sep 26 2017):

> Conjecture: all terms but the first term are multiples of 5. - _Harvey P. Dale_, Sep 26 2017

FORMULA (`%F`, verbatim):

> a(n)=A066388(n)/6.

The literal claim is
`∀ n : ℕ, IsMember(n) → n = 1 ∨ 5 ∣ n`, where `IsMember(n)` means
`1 ≤ n ∧ Prime(6n−1) ∧ Prime(6n+1) ∧ Prime(12n−1) ∧ Prime(12n+1)`.
Lean natural-number subtraction truncates in general, but the hypothesis `n ≥ 1`
keeps each displayed subtraction equal to ordinary subtraction here.

## Motivation

Dale's 2017 comment asserts that every sequence member after the first is a
multiple of five. The formal result proves the unbounded implication for every
natural number satisfying the four primality conditions.

## Gap

The dated surfaces recorded in preregistration issue #7568 and its probe on
2026-09-13 were OEIS history revisions #1 through #11, with revision #10
introducing Dale's conjecture and no proof recorded through revision #11.
Exact arXiv searches for `A177680` and `A066388` returned 0, and arXiv:2608.11941
contained no identifier hit. The google-deepmind/formal-conjectures search
returned 0. The epoch-research/LeanOpenProblems main tree returned 0 across
1628 paths; its results-tree listing was truncated at 47042 paths and is not
exhaustive. MathOverflow and Stack Exchange searches returned 0. OpenAlex was
blocked by rate limiting and is ASSUMED-UNVERIFIED. In pinned Mathlib,
`Nat.Prime.eq_one_or_self_of_dvd` is reused, but no complete implication was
found. The argument is elementary, and no priority claim is made.

## Route

Classify `n` modulo five. If `n ≡ 1 (mod 5)`, then `5 ∣ 6n−1`; primality forces
`6n−1 = 5`, hence `n = 1`. If `n ≡ 2 (mod 5)`, then `5 ∣ 12n+1`; primality
forces `12n+1 = 5`, which is impossible for `n ≥ 1`. If `n ≡ 3 (mod 5)`, then
`5 ∣ 12n−1`; primality forces `12n−1 = 5`, again impossible. If
`n ≡ 4 (mod 5)`, then `5 ∣ 6n+1`; primality forces `6n+1 = 5`, also impossible.
The remaining residue is zero, so `5 ∣ n`.

## Falsifier

A natural number `n ≥ 1` for which all four displayed neighbors are prime while
`n ≠ 1` and `5 ∤ n` would refute the theorem.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive.lean`.
- Main theorem: `dale_a177680`, with std3 axiom closure `[propext, Quot.sound]`.
- The orchestrator checked `1 ≤ n ≤ 10^6`: there are 502 members, the first
  eight are 1, 5, 110, 135, 355, 425, 555, and 565, matching `%S`; all except
  `n = 1` are multiples of five, with 0 counterexamples.
- The probe obtained the same readings with an exact integer sieve through
  12000001.
- The converse is false at `n = 10`, since `12·10−1 = 119 = 7·17`; the converse
  is not claimed.

## Triage

`theorem`

## ASSUMED-UNVERIFIED

OpenAlex was rate-limited, the literature search is bounded, and no priority
claim is made. The truncated LeanOpenProblems results-tree listing is not an
exhaustive search of that tree.
