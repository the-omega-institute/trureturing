---
slug: oeis-a335925-self-referential-quotient-first-occurrence
bibkey: alkan2020a335925
doi: null
url: https://oeis.org/A335925
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence
---

# First occurrences in the A335925 self-referential quotient recurrence

## Problem

OEIS A335925, NAME (`%N`, verbatim):

> a(n) = a(floor((n-1)/a(n-1))) + 1 with a(1) = 1.

COMMENT (`%C`, verbatim; Altug Alkan, Jun 30 2020):

> Least k such that a(k) = n are 1, 2, 5, 16, 65, 326, 1957, ... (Conjecture: This sequence is A000522).

Here A000522(0) = 1 and A000522(m) = m*A000522(m-1) + 1. The phrase
"least k such that a(k) = m" is formalized as a hit at that index together
with minimality among every positive index carrying m.

## Motivation

This OEIS conjecture was recorded in 2020 and remained unchanged through the
bounded source and literature checks recorded in preregistration issue #7464.
The full unbounded hit-and-minimality statement resolves the conjecture rather
than only extending its finite table.

## Gap

The search surfaces recorded in #7464 on 2026-09-13 returned the exact OEIS
token only for A335925. Exact identifier searches reported OpenAlex 0,
Crossref 0, DataCite 0, arXiv 0, MathOverflow 0, Math.SE 0, and GitHub code 0
apart from a directory mirror. The subsequent probe recorded the same zero-hit
literature result. These are bounded searches, not exhaustive coverage or a
priority claim.

## Route

Let T(0)=1 and T(r+1)=(r+1)*T(r)+1. The corrected block invariant is
`a(T(r)) = r+1`; for `T(r) <= n < T(r+1)`, the value `a(n)` belongs to
`{r,r+1}`; and `a(n)=r` implies `n < r*T(r)`. This corrected indexing was
re-preregistered in #7464 before Stage B. A two-step induction on r, with an
inner `Nat.le_induction` on n, establishes the block statement. Quotient-index
bounds use `Nat.div_lt_iff_lt_mul`. The value at the block start gives the hit,
and the block bound excludes every earlier positive occurrence.

## Falsifier

One positive m whose least positive index k satisfying `a(k)=m` differs from
T(m-1) would contradict the theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.lean`.
- Main theorem: `alkan_a335925`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator evaluated the recurrence through n = 2*10^6. The first
  occurrences for m = 1 through 9 were 1, 2, 5, 16, 65, 326, 1957, 13700,
  and 109601.
- The search seat evaluated through n = 10^7 for m <= 11 with no mismatch,
  and compared the supplied b-file at 10000/10000 entries. These finite checks
  support but do not replace the universal proof.

## Triage

`theorem`. The formal result proves both existence at T(m-1) and minimality for
every positive m.

## ASSUMED-UNVERIFIED

None beyond the bounded literature-search scope recorded above. In particular,
the zero-hit searches do not establish exhaustive literature coverage or
first-publication priority.
