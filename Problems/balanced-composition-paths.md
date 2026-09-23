---
slug: balanced-composition-paths
bibkey: wiseman2018a026010
doi: null
url: https://oeis.org/A026010
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BalancedCompositionPaths.result
---

# Balanced Compositions and Nonnegative Walks from Height Two

## Problem

OEIS A026010 is defined by

> a(n) = number of (s(0), s(1), ..., s(n)) such that s(i) is a nonnegative
> integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n and s(0) = 2

and carries a comment by Gus Wiseman dated Mar 17 2018, still standing at
revision #55 of Oct 13 2025:

> Conjecture: a(n) is the number of integer compositions of n + 2 in which the
> even parts appear as often at even positions as at odd positions (confirmed up
> to n = 19).

## Motivation

The frozen theorem `D5/S3/Combinatorics/BalancedCompositionPaths.result`
settles the comment for every `n`, with both sides stated as cardinalities of
the literal objects rather than as recursions.

## Gap

Issue 9460 records the screen carried out before the work. A026010 and its
cross-references A026009, A050168, A037952, A051924 and A097613 appear nowhere
under `Problems/`, `D5/`, `Library/`, `docs/` or the screening records in this
repository. The entry carries the comment unchanged and records no proof. The
partition analogues A300787 and A300788 are different statements and carry no
proof; A300789 carries a separate unproved conjecture of the same author about
domino tileability. Searches for a published proof connecting these
compositions to lattice paths returned nothing. Citation indices were not
exhaustively reachable, so this is a bounded negative finding.

## Route

Write `w` for the unrestricted walk kernel on the integers: `w 0` is the
indicator of the origin and `w (n+1) z = w n (z-1) + w n (z+1)`. It is even in
`z` and is Pascal's array in displacement coordinates.

**The walk side, by reflection.** The sequences from height two that never go
below zero are all sequences minus those that touch `-1`. Reflecting across that
line matches the offending sequences with all sequences from `-4`. Summing over
the end height telescopes, because the subtracted index exceeds the added one by
exactly three, and what survives is a sum of three consecutive kernel entries.

**The composition side, by a window of width six.** Recursion on the first part
splits a composition three ways: a first part of at least three loses two and
keeps every position and parity; a first part of one is deleted, which shifts
every remaining position by one and so negates the remaining balance; a first
part of two contributes one to the balance before being deleted, leaving `1-b`.
Tracking the signed difference `b` between the number of even parts at odd
positions and at even positions, the count at difference `b` equals the sum of
the six consecutive kernel entries from `3b-3` to `3b+2`.

**The identity.** At `b = 0` the six-entry window folds, by evenness of the
kernel, into `w 0 + 2 w 1 + 2 w 2 + w 3`, and the reflected walk sum at height
two is that same expression term by term.

No generating function, no square root and no real analysis enter. An earlier
route through the constant term of an algebraic generating function gives the
same closed forms — the discriminant collapses because `1 - 6y + 9y^2 - 4y^3`
factors as `(1-y)^2 (1-4y)` — but the kernel window is the cheaper argument and
is what the formal proof follows.

**Faithfulness.** Both sides are stated as cardinalities of the literal objects:
the walk count is the cardinality of an explicit finite set of height sequences
indexed by `Fin (n+1)`, and the composition count is the cardinality of a filter
on the compositions of `n + 2`. Bridges from those cardinalities to the
recursions are part of the proof rather than assumed.

## Falsifier

A composition whose even parts balance but which the predicate rejects, or a
height sequence inside the stated bounds that the finite set misses, would break
the reading. The bound is not binding: a valid sequence of length `n + 1` from
height two never exceeds `n + 2`, checked directly. A different position
convention would give a different left-hand count; the entry's own worked list
excludes it.

## Evidence

The two sides were computed independently — a height recursion for the walks, a
position-parity recursion for the compositions — and agree for every `n = 0..30`
against each other, where the author reports confirmation to `n = 19`. Both
closed forms were then checked against those computations and against the
entry's own data line for `n = 0..33`; all four agree. The predicates actually
written in the formal statement were re-enumerated separately and agree with the
data line for `n = 0..14`, with the height bound never binding.

The reading was aligned term by term with the entry's own worked example: for
`n = 3` the seven compositions of five are `(5)`, `(3,1,1)`, `(1,3,1)`,
`(1,1,3)`, `(2,2,1)`, `(1,2,2)`, `(1,1,1,1,1)`. The predicate rejects `(2,1,2)`
and accepts `(1,2,2)`, as it must.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9460
before the work. The computational use is `none`: no declaration is a bounded
enumeration, a checker, a numeric reduction or a certified instance, and the
delivered statement is universally quantified over all `n`.

## ASSUMED-UNVERIFIED

The literature screen is bounded. The entry was read in full at revision #55;
its cross-references and the partition analogues were checked; searches for a
published proof returned nothing. Citation indices and printed sources were not
exhaustively reachable, so no worldwide priority claim is made.
