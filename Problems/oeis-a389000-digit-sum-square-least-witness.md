---
slug: oeis-a389000-digit-sum-square-least-witness
bibkey: wu2025a389000
doi: null
url: https://oeis.org/A389000
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness
---

# The least simultaneous digit-sum witness in A389000

## Problem

> Conjecture: a(9m+5) = 210^(2*m+1)-1 for m >= 0.

— Chai Wah Wu, Oct 01 2025. The OEIS rendering means
`2·10^(2m+1) − 1`. Here `a(n)` is the least positive integer `k` such that
`n` divides both the base-10 digit sum of `k` and that of `k^2`.
The entry was created Sep 22 2025.

## Motivation

This is a first-tier recent OEIS conjecture selected by the search seat.
KPI = open problems resolved. The target is the full unbounded formula,
including leastness, for every natural index `m`.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-08 and searching by identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those searches. Absence of a proof in that scope does
not establish exhaustive literature coverage or first-publication priority.

## Route

Put `n = 9m+5`, `L = 2m+1`, and `K = 2·10^L − 1`. Both `K` and `K^2` have
digit sum `2n`, so `K` satisfies the two divisibility conditions. For
`0 < k < K`, the leading-digit ceiling and its rigid equality case give
`0 < digitSum k < 2n`; divisibility by `n` therefore forces `digitSum k = n`.
The mod-9 congruence gives `digitSum(k^2) ≡ n^2 ≡ 7 (mod 9)`. Writing
`digitSum(k^2) = nt` gives `5t ≡ 7 (mod 9)`, hence `t ≥ 5` and
`digitSum(k^2) ≥ 5n`. But `k^2 < 4·10^(2L)` gives the contrary ceiling
`digitSum(k^2) ≤ 18L+3 = 36m+21 < 5n`. Thus `K` is least.

## Falsifier

A counterexample index `m ≥ 0` with `a(9m+5) ≠ 2·10^(2m+1) − 1` would
contradict the assertion. This could be witnessed by a smaller positive `k`
satisfying both divisibilities, or by failure of the proposed candidate.
The orchestrator's exact check is supporting evidence only; it does not
replace the universal proof and was not repeated by this seat.

## Evidence

- Lean module: `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.lean`.
- Main theorem: `wu_conjecture`.
- Public companions in that module: `digitSum_witness`, `digitSum_witness_sq`.
- The brief also requested companion labels `wu_conjecture_one`,
  `altRowSum_succ_sub`, and `fib_cassini_two`; none is declared in the target
  module, so they are not evidence for this resolution.
- The implementation-seat envelope reports all three public theorems have
  exactly the std3 axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Triage

`theorem`. The formal proof establishes the complete least-witness formula
recorded in the OEIS conjecture, for every natural `m`.

## ASSUMED-UNVERIFIED

The quotes, definition, attribution, and dates were supplied by the
orchestrator. The OEIS revision history was read by the search seat, not by
this seat. The reported literature scope was the OEIS entry/history and
identifier searches on arXiv, MathOverflow, and GitHub on 2026-09-08; this
seat performed no network verification. No exhaustive literature or priority
claim follows. The std3 report and the orchestrator's exact check were
supplied evidence, not computations performed by Stage-B. Source-to-Lean
identification is not itself a kernel-checked fact.
