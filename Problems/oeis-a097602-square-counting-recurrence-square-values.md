---
slug: oeis-a097602-square-counting-recurrence-square-values
bibkey: zumkeller2004a097602
doi: null
url: https://oeis.org/A097602
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions
---

# Square values in the A097602 square-counting recurrence

## Problem

OEIS A097602, NAME (`%N`, verbatim):

> a(n+1) = a(n) + number of squares so far; a(1) = 1.

COMMENT (`%C`, verbatim):

> Conjecture: a(n) = m^2 iff m mod 3 > 0.

COMMENT (`%C`, verbatim):

> a(n) is a square iff n is congruent to {1, 4} mod 9. - _Vladeta Jovovic_, Aug 30 2004

FORMULA (`%F`, verbatim):

> a(9*n+1) = (3*n+1)^2; a(9*n+4) = (3*n+2)^2.

The conjecture is read as a statement about attained values: for every positive
m, the value m^2 occurs as a(n) at some positive index n if and only if 3 does
not divide m. The literal reading with independent free n and m is false: at
n=2 the sequence has a(2)=2, while for example m=1 makes the right side true
and a(2)=m^2 false.

## Motivation

The square-value conjecture was recorded in 2004 and remained labelled as a
conjecture through the bounded source and literature checks recorded in
preregistration issue #7497. The universal theorem classifies every square
value of the recurrence, rather than extending only its finite table.

## Gap

The searches recorded in #7497 and its probe on 2026-09-13 read OEIS history
revisions #1 through #22, which only restate the assertions and contain no
proof. Exact searches reported OpenAlex 0 and MathOverflow 0; GitHub results
were OEIS mirrors. The arXiv API and Semantic Scholar each returned HTTP 429
on the initial request and the required retry. These are bounded searches, not
exhaustive literature coverage or a priority claim.

## Route

Write c(n) for the number of square values among a(1),...,a(n). A nine-periodic
block invariant gives
`a(9*k+1)=(3*k+1)^2`, `c(9*k+1)=2*k+1`,
`a(9*k+4)=(3*k+2)^2`, `c(9*k+4)=2*k+2`, and carries the next block start
`a(9*k+10)=(3*k+4)^2`, `c(9*k+10)=2*k+3`. The seven interior terms are
sandwiched strictly between consecutive squares. Projecting this invariant
gives the square positions. The square values then follow from
`{(3*k+1)^2, (3*k+2)^2 : k in Nat} = {m^2 : 3 does not divide m}`.

## Falsifier

One n>=1 for which `IsSquare(a(n))` holds but `n mod 9` is neither 1 nor 4,
or conversely, would contradict the position theorem. One positive m not
divisible by 3 whose square is never attained, or one positive m divisible by
3 whose square is attained, would contradict the value theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/SquareCountingRecurrenceSquarePositions.lean`.
- Position theorem: `jovovic_a097602_positions`.
- Value theorem: `zumkeller_a097602`.
- Both theorems use std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator evaluated the recurrence through n=20000. The position
  characterization and both displayed `%F` formulas had no mismatches.
- The probe independently evaluated the same range. The square roots attained
  were exactly `{m <= 6667 : 3 does not divide m}`, comprising 4445 roots.

## Triage

`theorem`. The value theorem proves the conjecture under its contextual value
reading; the position theorem proves the adjacent unlabelled assertion.

## ASSUMED-UNVERIFIED

The arXiv API and Semantic Scholar searches remain unverified because both
requests returned HTTP 429 twice. The literature search is bounded; no claim
of exhaustive coverage or first-publication priority is made.
