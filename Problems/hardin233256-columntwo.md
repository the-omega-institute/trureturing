---
slug: hardin233256-columntwo
bibkey: hardin2013a233256
doi: null
url: https://oeis.org/A233256
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnTwo.result
---

# Hardin's second-column recurrence for A233256

## Problem

[OEIS A233256](https://oeis.org/A233256), revision 6, gives:

> Empirical for column k:
> k=2: a(n) = 20*a(n-1) -64*a(n-2)

The count `a n` literally filters all `Fin n × Fin 2 → Fin 6`. Each row
has its horizontal bond, and consecutive rows have the antidiagonal bond
from the old right cell to the new left cell. Each bond excludes equal
colours and colours summing to five. The first cell is zero; every 2, 3
or 4 has an earlier 1, and every 3 an earlier 2 in row-major order.
The assertion is `a n = 20*a(n-1) - 64*a(n-2)` in integers for every
`n ≥ 3`.

## Motivation

The settling declaration is `HardinA233256ColumnTwo.result`, under the
preregistration [#28883](https://github.com/the-omega-institute/trureturing/issues/28883).
The source note is `Library/Automata/hardin2013a233256.md`.

## Gap

The source labels the recurrence empirical and supplies no proof.

## Route

The public width-two transfer of `HardinA233251TriangleStrip` counts the
literal filter. The scanner boundary stores the seen-colour flags and
the pair label of the right cell. The reachable-state predicate is
preserved by every legal row. On those states a finite kernel certificate
gives `v 2 = 20*v 1 - 64*v 0`; linearity and induction give the same
identity at every continuation index. The sum over legal first rows
shifts the array index by one.

## Falsifier

A literal count at any `n ≥ 3` violating the displayed equality would
contradict `result`.

## Evidence

`HardinA233256ColumnTwo.result` proves the recurrence together with
`a 1 = 1`, `a 2 = 10`, `a 3 = 136`. Its axiom closure is
`{Classical.choice, Quot.sound, propext}`. The b-file uses antidiagonal
index `(n+k-2)*(n+k-1)/2+n`; all available second-column entries, heights
1 through 20, satisfy the recurrence where applicable.

## Triage

The second-column recurrence is proved for every `n ≥ 3` by `result`.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified. The
bounded literature screen is recorded in #28883. Other table slices are
outside this assertion.
