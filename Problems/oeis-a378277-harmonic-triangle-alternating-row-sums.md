---
slug: oeis-a378277-harmonic-triangle-alternating-row-sums
bibkey: schulte2024a378277
doi: null
url: https://oeis.org/A378277
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums
---

# Alternating row sums of the Fibonacci harmonic triangle

## Problem

OEIS A378277 records the following conjecture:

> Conjecture: Alt. row sums of the harmonic triangle are Fibonacci(n-2) / Fibonacci(n+1), where Fibonacci(-1) = 1.

Werner Schulte, Nov 21 2024.

Its FORMULA gives the denominators:

> T(n, k) = Fibonacci(n) * Fibonacci(n+1) if k = n, and Fibonacci(k) * Fibonacci(k+2) if 1 <= k < n.

The harmonic triangle has entries `1 / T(n, k)` for `1 <= k <= n`.
Write `F(n) = Nat.fib n` and
`S(n) = sum_{k=1}^n (-1)^(k-1) / T(n, k)`, with the first term positive.

## Motivation

This is a first-tier recent OEIS conjecture selected in the implementation
brief. The KPI is open problems resolved. The target is the assertion for
every positive row, not a finite collection of numerical instances.

## Gap

The supplied search-seat report records no proof found: the OEIS entry and
revision history were read on 2026-09-08, and identifier searches were made
on arXiv, MathOverflow, and GitHub. This Stage-B seat has no network access
and did not independently repeat those searches. No-hit results in that
scope do not establish first-publication priority or an exhaustive literature
search. The missing argument is the universal moving-diagonal row identity.

## Route

The unchanged row prefix cancels. Moving the diagonal replaces its old
denominator and adds the next diagonal term, giving, for `n >= 2`,
`S(n+1) - S(n) = 2(-1)^n / (F(n+1)F(n+2))`.
The quotient has the same increment by the Cassini-type identity
`F(n-1)F(n+1) - F(n-2)F(n+2) = 2(-1)^n`.
This identity is bound from the frozen `D5/S1/Recurrence/FibVajda` theorem
`fib_vajda`, specialized at `i = 1`, `j = 3`; the public companion uses the
nonnegative reindexing `n = m + 2`. Induction from `n = 2` proves the formula
for every `n >= 2`. The row `n = 1` is handled separately as `S(1) = 1`,
realizing the source convention `F(-1) = 1` without a negative natural index.

## Falsifier

A counterexample index `n >= 2` with
`S(n) != F(n-2) / F(n+1)`, or a failure of `S(1) = 1`, would contradict the
assertion. The orchestrator's exact numerical check is supporting evidence
only; finite checks do not prove the universal statement.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.lean`.
- Main theorem: `schulte_conjecture`.
- Companions: `schulte_conjecture_one`, `altRowSum_succ_sub`, `fib_cassini_two`.
- Definitions: `denominator` and the rational-valued `altRowSum`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat's `#print axioms` for all four public theorems.
- The orchestrator reported verification of `make lean`, `make lean-report`,
  and `make emit` before the Stage-B edits; this is attributed evidence,
  not a claim that Stage-B executed those commands.

## Triage

`theorem`. The main theorem and separate first-row companion close the
positive-row assertion recorded by OEIS.

## ASSUMED-UNVERIFIED

The verbatim conjecture and FORMULA quotes were supplied by the orchestrator.
The OEIS entry and revision history were read by the search seat on
2026-09-08, not by this Stage-B seat. The reported literature scope was the
OEIS entry and revision history plus identifier searches on arXiv,
MathOverflow, and GitHub; this seat had no network access. Exhaustive
literature coverage, first-publication priority, and the source-to-Lean
identification are not kernel-checked facts.
