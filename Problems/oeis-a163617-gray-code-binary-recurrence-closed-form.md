---
slug: oeis-a163617-gray-code-binary-recurrence-closed-form
bibkey: yanev2016a163617
doi: null
url: https://oeis.org/A163617
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm
---

# A Gray-code closed form for the A163617 binary recurrence

## Problem

OEIS A163617, `%N` (verbatim):

> a(2*n) = 2*a(n), a(2*n + 1) = 2*a(n) + 2 + (-1)^n, for all n in Z.

FORMULA (verbatim; Velin Yanev, Dec 17 2016):

> Conjecture: a(n) = A003188(n) + (6*n + 1 - (-1)^n)/4.

OEIS A003188, `%N` (verbatim), followed by its `%F` XOR formula:

> Decimal equivalent of Gray code for n.

> a(n) = n XOR floor(n/2), where XOR is the binary exclusive OR operator.

Only the natural-number half, initialized by `a(0) = 0`, is formalized. The
negative-index half is OEIS A163618 and is not claimed.

## Motivation

This first-tier OEIS conjecture was recorded in 2016. The target is its full
unbounded closed form for every nonnegative index of the A163617 recurrence,
with the cited Gray-code component and parity correction kept explicit.

## Gap

The preregistration issue records searches dated 2026-09-13 over the current
OEIS entry and revisions after revision 27, its 16 reverse references,
Crossref, Google Scholar, DuckDuckGo, arXiv, MathOverflow, GitHub, and the
repository. A proof or refutation was not found in the checked surfaces.
This bounded search does not establish exhaustive literature coverage or
first-publication priority.

## Route

Apply binary induction via `Nat.evenOddRec`. For `n = 2m` and `n = 2m+1`,
the Gray code satisfies the local shift identities obtained from Mathlib's
`Nat.xor_bit`, while the parity correction obeys the two corresponding
recurrence branches. The invariant `a n = gray n + corr n` is then carried
through the custom recurrence from the initial value `a 0 = 0`.

## Falsifier

A natural number `n` for which `a n != gray n + corr n` would contradict the
assertion. A mismatch in either binary branch, the initial value, or the
identification of `gray` or `corr` with the cited formulas would invalidate
the proposed resolution. Finite exact checks are supporting evidence only and
do not replace the universal proof.

## Evidence

- Lean module: `D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.lean`.
- Main theorem: `yanev_a163617 : forall n, a n = gray n + corr n`.
- Public definitions: `a`, `gray`, and `corr`.
- The canonical Lean report gives the theorem exactly the std3 axioms:
  `propext`, `Classical.choice`, and `Quot.sound`.
- The orchestrator's exact check found zero mismatches for `0 <= n < 5000`.
- The probe checked the same range and recorded `a(4999) = 14223`.
- The search seat checked through `n <= 10^4`, including
  `a(10000) = 28464 = 13464 + 15000`.
- This implementation seat independently repeated both finite ranges with
  zero mismatches and reproduced both displayed endpoint values.

## Triage

`theorem`. The Lean theorem proves the nonnegative-index closed form at every
natural number. It does not assert the separate negative-index sequence.

## ASSUMED-UNVERIFIED

The external search counts beyond the OEIS entries are supplied by
preregistration issue 7413 and were not independently repeated by this
implementation seat. The literature search is bounded, so exhaustive coverage
and publication priority remain unverified. The module kernel-checks
`(corr n : ℤ) = (6n + 1 − (−1)^n)/4` as an `example` immediately after the
definition of `corr`.
