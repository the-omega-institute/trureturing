---
slug: oeis-a181278-barker-binary-gram-recurrence-refutation
bibkey: barker2018a181278
doi: null
url: https://oeis.org/A181278
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.result
---

# Refutation of Barker's A181278 recurrence

## Problem

OEIS A181278 defines the sequence as follows:

> Number of 2 X n binary matrices M with rows in strictly increasing order and rows of M*Mtranspose (mod 2) in strictly decreasing order.

Colin Barker's FORMULA line of March 27, 2018 states verbatim:

> a(n) = 4*a(n-1) + 4*a(n-2) - 16*a(n-3) for n>3.

The offset is 1, so `a(1) = 0` is a sequence term. For natural-valued terms,
the subtraction-free formal claim is the equivalent assertion
`a(n) + 16*a(n-3) = 4*a(n-1) + 4*a(n-2)` for every `n >= 4`.

## Motivation

Issue #8435 preregistered this first-tier OEIS conjecture, its verbatim source,
full quantifiers, expected bind-only proof shape, and the counterexample at
`n = 4`. A kernel-checked counterexample resolves the literal published
recurrence without asserting a replacement theorem.

## Gap

The checked OEIS entry contains no proof, refutation, reference section, or
settlement marker for this recurrence; its only linked data source is the
sequence b-file. Searches for A181278, A181274, the recurrence shape, and the
binary Gram-row counting shape found no settlement theorem in the repository
or pinned Mathlib. The bounded external Lean-code search found only a
synthetic sequence definition with no counting equivalence or theorem.

These checked surfaces do not establish exhaustive literature coverage or
publication priority.

## Route

Represent each length-`n` binary row by a natural number below `2^n`. For a
pair of rows, finite filtering computes the two row parities and their common
set-bit parity. The strict inequalities compare the source rows and the two
Gram rows lexicographically, with the first Gram entry as the high digit.

Kernel reduction gives `a(1) = 0`, `a(2) = 3`, `a(3) = 11`, and `a(4) = 48`.
The claim at `n = 4` would instead require
`48 + 16*0 = 4*11 + 4*3 = 56`, a contradiction.

## Falsifier

A faithful proof of the stated recurrence for every natural `n >= 4` would
falsify this refutation. A correction to the A181278 counting interpretation
or to any of the four kernel-computed values would require rechecking the
claimed counterexample against the source.

## Evidence

- Lean module:
  `D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.lean`.
- Resolution theorem: `result : Not claim`; the `Refuted` resolution claim is
  attached only to this theorem.
- The definition enumerates all ordered row pairs in
  `List.range (2^n).product (List.range (2^n))` and counts exactly those
  satisfying the two strict lexicographic conditions.
- The first eight exact counts are
  `0, 3, 11, 48, 188, 768, 3056, 12288`, matching the published sequence.
- The theorem uses `decide +kernel` for the four finite counts and closed
  arithmetic, and uses no repository theorem as a premise.

## Triage

`theorem`. The certified instance at `n = 4` refutes the literal universal
recurrence. It asserts no corrected threshold, generating function, closed
form, or claim about any other index.

## ASSUMED-UNVERIFIED

The correspondence between the OEIS prose and the formal row encoding is a
source-faithfulness judgment, not a kernel theorem. The bounded literature
search does not establish exhaustive coverage or publication priority. Exact
transfer computation supports that `n = 4` is the only failure and that the
recurrence holds from `n = 5`, but neither statement is formalized here.
