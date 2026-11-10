---
slug: hardin233256-rowone
bibkey: hardin2013a233256
doi: null
url: https://oeis.org/A233256
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256RowOne.result
---

# Hardin's first-row recurrence for A233256

## Problem

[OEIS A233256](https://oeis.org/A233256), revision 6, gives:

> Empirical for row n:
> n=1: a(n) = 6*a(n-1) -8*a(n-2) for n>3

The count `a k` literally filters all `Fin 1 × Fin k → Fin 6`. Its
horizontal path bonds exclude equal colours and colours summing to five.
The first cell is zero; every 2, 3 or 4 has an earlier 1, and every 3 an
earlier 2. There are no antidiagonal bonds. The assertion is
`a k = 6*a(k-1) - 8*a(k-2)` in integers for every `k ≥ 4`.

## Motivation

The settling declaration is `HardinA233256RowOne.result`, under the
preregistration [#28883](https://github.com/the-omega-institute/trureturing/issues/28883).
The source note is `Library/Automata/hardin2013a233256.md`.

## Gap

The source labels the recurrence empirical and supplies no proof. Its
lower bound is essential: at width three the right side is `-2`, whereas
the literal count is `3`.

## Route

Transposition preserves the path and the cell order, identifying the
literal filter with a width-one transfer from `HardinA233251TriangleStrip`.
The scanner state stores the seen-colour flags and the final pair label.
The reachable-state predicate is preserved by every legal step. After
one continuation step a finite kernel certificate gives
`v 3 = 6*v 2 - 8*v 1`; induction propagates it. The first-cell sum shifts
the array index by one, yielding the recurrence from width four.

## Falsifier

A literal count at any `k ≥ 4` violating the displayed equality would
contradict `result`.

## Evidence

`HardinA233256RowOne.result` proves the recurrence; `HardinA233256RowOne.finite_certificate` proves `a 1 = 1`, `a 2 = 1`, `a 3 = 3`, `a 4 = 10`. Its axiom closure is
`{Classical.choice, Quot.sound, propext}`. The b-file uses antidiagonal
index `(n+k-2)*(n+k-1)/2+n`; all available first-row entries, widths
1 through 22, satisfy the recurrence where applicable.

## Triage

The first-row recurrence is proved for every `k ≥ 4` by `result`.

### What the settlement shows

1. **Follows from the proved recurrence and certified initial values (not kernel-checked):**
   $T(1,k)=(4^k+4\cdot2^k)/32$ for every $k\ge3$; the recurrence fails at
   $k=3$ because $T(1,2)=1$ is not on this curve (it would be $3/8$).
2. **Computed:** $T(1,2n)=T(n,2)$ (see the column-two dossier).

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified. The
bounded literature screen is recorded in #28883. Other table slices are
outside this assertion.
