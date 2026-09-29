---
slug: mathar-2012-a108958-recurrence
bibkey: mathar2012a108958
doi: null
url: https://oeis.org/A108958
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.result
---

# Mathar's recurrence for the zero-quantum transition pairs A108958

## Problem

OEIS A108958 counts the unordered pairs of distinct binary words of length
`n` with the same number of 1's, `a(n) = Σ_{k=0}^{n} C(C(n,k), 2)`; for `n`
spins 1/2 these are the nontrivial zero-quantum transitions. Its formula
field records:

> Conjecture: n*(n-2)*a(n) +2*(-3*n^2+7*n-3)*a(n-1) +4*(n-1)*(2*n-3)
> *a(n-2)=0. - _R. J. Mathar_, Apr 04 2012

Issue #10598 fixes the reading: `a` is defined by the entry's first formula
line (also at `n = 0`, value `0`), and the recurrence is asserted for every
`n ≥ 2`.

## Motivation

The entry still marks the recurrence as a conjecture (revision 77,
2025-11-05). `D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.result` proves
it for every `n ≥ 2`.

## Gap

Issue #10598 preregisters the proof route and the literature check. The entry
gives the closed form `binomial(2n−1, n−1) − 2^(n−1)` (Jovovic, 2005) but no
proof of the recurrence; the repository has no declaration about A108958.
`not-found-in-searched-scope`.

## Route

1. `2 a(n) = Σ_k C(n,k)^2 − Σ_k C(n,k) = C(2n, n) − 2^n`.
2. `u(n) = C(2n, n)` satisfies `n u(n) = 2(2n − 1) u(n − 1)`, which makes
   the three-term recurrence for `u` an identity in `u(n − 1)`.
3. `w(n) = 2^n` satisfies the recurrence identically, and the recurrence is
   linear, so `a = (u − w)/2` satisfies it.

## Falsifier

The proof would fail if the closed form of step 1 or the identities of steps
2 and 3 failed for some `n ≥ 2`.

## Evidence

Exact integer computation: the recurrence holds for `n = 2, …, 299` and
`2 a(n) = C(2n, n) − 2^n` for `n = 0, …, 199` (issue #10598).

The canonical source is
`D5/S3/Combinatorics/ZeroQuantumPairsRecurrence.lean`.
Its public declarations are `a`, `claim`, and `result`. The frozen module
state has statement identity
`sha256:927b7ebb2138f5fbeb71a382fe8b6aa929e43e643e921f62891077b6f983bc13`.
The result declaration has statement identity
`sha256:a40591f2537a002a1a0b9eec820b55ae6b03587e44c472b212532221be2ca8ec`.
The Freeze event is
`sha256:536825db74874f9d1e59f65a453748cddc2d8d8441b75ef0a2ca324a6786268a`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture (OEIS formula field), preregistered in issue
#10598 before the probe. `theorem`; resolution `proved`. The public theorem
has `proof_shape: bind-only`: every atomic fact is an instance of a pinned
Mathlib lemma (the Vandermonde sum of squares, the binomial sum and the central
binomial recurrence), combined by sum distribution and linear arithmetic. The
settlement of the named conjecture is the new content, so the admission basis
is `open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
