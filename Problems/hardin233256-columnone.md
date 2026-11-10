---
slug: hardin233256-columnone
bibkey: hardin2013a233256
doi: null
url: https://oeis.org/A233256
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233256ColumnOne.result
---

# Hardin's first-column recurrence for A233256

## Problem

[OEIS A233256](https://oeis.org/A233256), revision 6, defines normalized
six-colour arrays with horizontal and antidiagonal complementary-pair
exclusion. Its FORMULA gives:

> Empirical for column k:
> k=1: a(n) = 12*a(n-1) -44*a(n-2) +48*a(n-3)

Here `a n` literally filters all `Fin n × Fin 1 → Fin 6`. There are no
bonds. The first cell is zero; every 2, 3 or 4 has an earlier 1, and every
3 an earlier 2. Colours need not occur. The assertion is, in integers,
`a n = 12*a(n-1) - 44*a(n-2) + 48*a(n-3)` for every `n ≥ 4`.

## Motivation

The settling declaration is `HardinA233256ColumnOne.result`, under the
preregistration [#28883](https://github.com/the-omega-institute/trureturing/issues/28883).
The source note is `Library/Automata/hardin2013a233256.md`.

## Gap

The source labels the recurrence empirical and supplies no proof.

## Route

The public width-one transfer of `HardinA233251TriangleStrip` counts the
literal filter using the shared first-occurrence scanner. The boundary
has two seen-colour flags and no bond data. Its continuation vectors
satisfy `v(n+3) = 12*v(n+2) - 44*v(n+1) + 48*v(n)`. A finite kernel
certificate gives the initial vector identity; linearity propagates it
by induction. Summing the legal first cells shifts the array index by one.

## Falsifier

A literal count at any `n ≥ 4` violating the displayed equality would
contradict `result`.

## Evidence

`HardinA233256ColumnOne.result` proves the recurrence together with
`a 1 = 1`, `a 2 = 3`, `a 3 = 11`, `a 4 = 48`. Its axiom closure is
`{Classical.choice, Quot.sound, propext}`. The b-file uses antidiagonal
index `(n+k-2)*(n+k-1)/2+n`; all available first-column entries, heights
1 through 21, satisfy the recurrence where applicable.

## Triage

The first-column recurrence is proved for every `n ≥ 4` by `result`.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified. The
bounded literature screen is recorded in #28883. Other table slices are
outside this assertion.
