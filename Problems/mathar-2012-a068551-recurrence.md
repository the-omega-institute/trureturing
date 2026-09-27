---
slug: mathar-2012-a068551-recurrence
bibkey: mathar2012a068551
doi: null
url: https://oeis.org/A068551
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/LatticeReturnsRecurrence.result
---

# Mathar's recurrence for the lattice-path returns A068551

## Problem

OEIS A068551 is `a(n) = 4^n − C(2n, n)`; by a comment of G. Critzer it counts
the returns to the axis in all ±1 lattice paths (random-walk bridges) from the
origin to `(2n, 0)`. Its formula field records:

> Conjecture: n*a(n) + 2*(3-4*n)*a(n-1) + 8*(2*n-3)*a(n-2) = 0. - _R. J.
> Mathar_, Apr 01 2012

Issue #10754 fixes the reading: `a` is the entry's name, the recurrence is
asserted for every `n ≥ 2` and read in `ℤ`.

## Motivation

The entry still marks the recurrence as a conjecture (revision 88,
2026-05-30). `D5/S3/Combinatorics/LatticeReturnsRecurrence.result` proves it
for every `n ≥ 2`.

## Gap

Issue #10754 preregisters the proof route and the literature check; the
entry's history records no proof, and the papers proving batches of Mathar's
conjectures do not treat A068551. `not-found-in-searched-scope`.

## Route

1. `u(n) = C(2n, n)` satisfies `n u(n) = 2(2n − 1) u(n − 1)` and `v(n) = 4^n`
   satisfies `v(n) = 4 v(n − 1)`.
2. For `a = v − u` the recurrence expression is
   `−R₀ + 4R₁ + nS₀ − 2(2n − 3)S₁`, a combination of those relations at
   `n` and `n − 1`.

## Falsifier

The proof would fail if the combination of step 2 did not reproduce the
recurrence expression for some `n ≥ 2`.

## Evidence

Exact integer computation: the closed form reproduces the 24 data terms, the
recurrence holds for `n = 2, …, 400`, and replacing the leading coefficient
`n` by `n + 1` fails for every such `n` (issue #10754).

The canonical source is `D5/S3/Combinatorics/LatticeReturnsRecurrence.lean`.
Its public declarations are `a`, `claim`, and `result`. The frozen module
state has statement identity
`sha256:63efba9e1d55b1e20c1d930cdcd7008a7c1b6a587aaf24b35dc5eec7d9944856`.
The result declaration has statement identity
`sha256:31cdb3f2429ee9bac33c93f979e5d7723e2f300ce1075473d39c41dedf3a1ef2`.
The Freeze event is
`sha256:b830b988010f2a68b8f01b75f6a91cf46bb7ef7bd828d2f77dfcb09385d0f543`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture (OEIS formula field), preregistered in issue
#10754 before the probe. `theorem`; resolution `proved`. The public theorem
has `proof_shape: bind-only`: every atomic fact is an instance of a pinned
Mathlib lemma (the central binomial recurrence and `pow_succ`), combined by
linear arithmetic. The settlement of the named conjecture is the new content,
so the admission basis is `open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
