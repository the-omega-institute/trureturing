---
slug: oeis-a329278-triangular-residue-descent-count
bibkey: kagey2019a329278
doi: null
url: https://oeis.org/A329278
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/TriangularResidueDescentCount
---

# The triangular-residue descent count in A329278

## Problem

OEIS A329278, NAME (verbatim):

> Irregular table read by rows. The n-th row is the permutation of {0, 1, 2, ..., 2^n-1} given by T(n,k) = k(k+1)/2 (mod 2^n).

COMMENT (verbatim; Peter Kagey, Nov 11 2019):

> Conjecture: for n > 0, the n-th row has 2^(n-1)-1 descents.

A descent is an index `k` with `0 <= k < 2^n - 1` and
`T(n,k) > T(n,k+1)`. The target concerns every positive natural `n`.

## Motivation

This 2019 OEIS conjecture asks for the exact number of adjacent strict
descents in every positive row of the triangular-number permutation modulo a
power of two. The theorem proves the full unbounded count rather than a finite
collection of rows.

## Gap

The checked surfaces on 2026-09-13 gave five OpenAlex results, all false
positives; zero exact MathOverflow identifier hits, while MathOverflow answer
507816 discusses the permutation but contains no descent count; zero exact
GitHub phrase hits; and zero matches in the pinned Mathlib tree and its
dependencies. The arXiv endpoint returned `Rate exceeded`, so arXiv was not
verified. No proof or refutation was found in the surfaces that completed.
This is a bounded search report, not an exhaustive literature or priority
claim.

## Route

Write `s_k = T(n,k)` and `M = 2^n`. The triangular-number identity

`k(k+1)/2 + (k+1) = (k+1)(k+2)/2`

gives `s_(k+1) = (s_k + (k+1)) mod M`; a wrap is equivalent to a descent.
Induction on `j <= M-1` then proves the prefix invariant

`card {k < j : T(n,k+1) < T(n,k)} = floor((j(j+1)/2)/M)`.

At the endpoint,
`(2^n-1)2^n/2 = (2^n-1) * 2^(n-1)`, so the quotient is
`2^(n-1)-1`.

## Falsifier

Any positive natural `n` whose row has a number of adjacent strict descents
different from `2^(n-1)-1` would refute the result. A failure of either the
wrap/descent equivalence or the prefix-quotient invariant would invalidate the
proof route.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/TriangularResidueDescentCount.lean`.
- Main theorem: `kagey_a329278 : forall n, 0 < n -> descents n =
  2^(n-1)-1`.
- Public definitions: `T` and `descents`.
- The theorem's axiom report is std3: `propext`, `Classical.choice`, and
  `Quot.sound`.
- The orchestrator checked `n = 1..16` with zero descent-count mismatches and
  also checked that each row is a permutation and has the stated endpoint.
- The probe checked `n = 1..20`, covering 2,097,150 entries, with zero
  descent-count mismatches.

## Triage

`theorem`. The Lean theorem proves the stated descent count for every positive
natural `n`, matching the scope of the OEIS conjecture.

## ASSUMED-UNVERIFIED

The OEIS quotation, attribution, external search results, and finite numerical
checks are external evidence rather than kernel-checked facts. The arXiv
surface was not verified because its endpoint was rate-limited. The completed
search was bounded to the surfaces listed in Gap, so no exhaustive literature
or first-publication claim follows. Source-to-Lean identification is not
itself a kernel-checked bibliographic fact.
