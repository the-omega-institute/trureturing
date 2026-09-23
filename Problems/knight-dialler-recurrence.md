---
slug: knight-dialler-recurrence
bibkey: barker2019a327692
doi: null
url: https://oeis.org/A327692
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/KnightDiallerRecurrence.result
---

# The Knight-Dialler Recurrence

## Problem

OEIS A327692 is defined by

> Number of length-n phone numbers that can be dialed by a chess knight on a 0-9
> keypad that starts on any number and takes n-1 steps

and carries, at revision #41 of Apr 22 2024, a formula line still labelled a
conjecture:

> Conjectures from _Colin Barker_, Oct 01 2019: (Start)
> G.f.: 2*x*(5 + 10*x - 7*x^2 - 8*x^3 + 2*x^4) / (1 - 6*x^2 + 4*x^4).
> a(n) = 6*a(n-2) - 4*a(n-4) for n>6. (End)

A later comment by Francesca Arici, dated Apr 17 2024, adds that the recurrence
also holds at `n = 6` and sketches a route through the eigenvalues of the
adjacency matrix, ending at "reduces to checking an algebraic condition on the
nonzero eigenvalues". The condition is not checked there and the formula line
was not reclassified.

## Motivation

The frozen theorem `D5/S3/Combinatorics/KnightDiallerRecurrence.result` settles
the recurrence for every `n`, with the count stated as the cardinality of the
literal set of dialable digit sequences rather than as a recursion.

## Gap

Issue 9492 records the screen carried out before the work. A327692 appears
nowhere under `Problems/`, `D5/`, `Library/` or `docs/` in this repository, apart
from a note-only row in the 2026-09-10 triage record. The entry itself still
labels the formula a conjecture. Its cross-references A280594 and A169696 carry
no proof of it. Searches return knight-dialler programming material, which counts
paths from a fixed start rather than the grand sum over all starts, and does not
address the closed recurrence. Citation indices were not exhaustively reachable,
so this is a bounded negative finding.

## Route

Write `u n` for the vector whose entry at digit `d` counts the dialable sequences
of `n` steps that start at `d`. Then `u 0` is all ones, `u (n+1)` is the knight
transfer step applied to `u n`, and `dial n`, the count over all starting digits,
is the sum of the entries of `u n`.

**The bridge.** The count is the cardinality of an explicit finite set of
sequences `Fin (n+1) → Fin 10`, and the fibre over the second entry of a sequence
starting at `i` is in bijection with the sequences of one step fewer starting at
that entry — delete the head, or prepend `i`. Counting fibrewise turns the
cardinality into the transfer step, and this is the part that is genuinely proved
rather than computed.

**The transfer step is linear**, so it carries the identity forward: from
`u (n+5) + 4 * u (n+1) = 6 * u (n+3)` entrywise at one place, the same identity
at the next place follows by summing the hypothesis against the neighbour
indicator.

**The base case is one evaluation.** In matrix language, the residual of the
recurrence applied to the all-ones vector is not zero,

    (A^4 - 6A^2 + 4I) · 1 = (0,0,0,0,0,4,0,0,0,0),

the entire residual sitting on the digit `5`; one further step annihilates it,
because `5` is the one key a knight can never leave, both of its knight images
being the blank cells `*` and `#`. That single fact is the whole content of the
recurrence. Concretely

    u 1 = (2,2,2,2,3,0,3,2,2,2)
    u 3 = (12,10,10,10,16,0,16,10,10,10)
    u 5 = (64,52,52,52,84,0,84,52,52,52)

and both sides of the base identity equal `(72,60,60,60,96,0,96,60,60,60)`.

It also fixes the exponent bookkeeping exactly. Summing the residual over all
starting digits gives `4` at `m = 5`, so the recurrence fails there —
`a(5) + 4*a(1) = 280` against `6*a(3) = 276` — and first holds at `m = 6`, which
is what the entry's later comment reports.

No eigenvalues, no diagonalisability and no real spectrum enter, so the route is
shorter than the one sketched on the entry.

**Faithfulness.** The statement is additive, `dial (n+5) + 4 * dial (n+1) =
6 * dial (n+3)`, because natural subtraction would truncate and silently weaken
it. In the entry's indexing `dial n` is `a(n+1)`, so this is `a(m) = 6*a(m-2) -
4*a(m-4)` for every `m >= 6`.

## Falsifier

A knight move the adjacency misses, or a pair of digits it wrongly joins, would
break the reading; the adjacency was rebuilt from the keypad coordinates rather
than copied, and its out-degrees are `0:2, 1:2, 2:2, 3:2, 4:3, 5:0, 6:3, 7:2,
8:2, 9:2`. Counting sequences from a fixed start rather than over all starts
would give a different left-hand side and a different recurrence. Stating the
recurrence with truncated subtraction would change it at the small arguments
where the identity is tightest.

## Evidence

The counts were computed from the coordinate-derived adjacency and reproduce the
entry's data line term by term over all 27 published terms, with no mismatch:
`dial (0..6) = 10, 20, 46, 104, 240, 544, 1256`. The additive identity was
checked directly for `n = 0..33`, with no failure, and the excluded case was
confirmed to fail: at `m = 5` the two sides are `280` and `276`. The two
displayed vector identities were computed over the integers, and the base-case
vectors `u 1`, `u 3`, `u 5` above were re-derived independently of the formal
proof.

One reading was checked before dispatch and is recorded because it is easy to
assume otherwise: the matrix identity `A^5 + 4A = 6A^3` is **false** — 32 entries
differ, for instance the entry at `(1,2)` is `8` on the left and `6` on the
right. Only the identity applied to the all-ones vector holds.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9492
before the work. The computational use is `none`: no declaration is a bounded
enumeration, a checker, a numeric reduction or a certified instance, and the
delivered statement is universally quantified over all `n`.

## ASSUMED-UNVERIFIED

The literature screen is bounded. The entry was read in full at revision #41 and
its cross-references were checked; searches for a published proof returned only
programming material on a different count. Citation indices and printed sources
were not exhaustively reachable, so no worldwide priority claim is made. The
weight of the result is stated plainly: the mathematics is elementary, and a
comment on the entry already asserts that a proof exists by graph-theoretic
means. What is settled is that the formula line was never converted, and that the
reason it holds is simpler than the route sketched there.
