---
slug: oeis-a289923-left-limit-nonnegativity
bibkey: kimberling2017a289923
doi: null
url: https://oeis.org/A289923
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative
---

# Nonnegativity of the A289923 left-limit sequence

## Problem

The source definition and conjecture are quoted in
`Library/Arith/kimberling2017a289923.md`.

The complete target includes existence and uniqueness of an integer sequence
whose nth coefficient is eventually constant throughout a left neighborhood of
19/21, for each natural n including zero, and nonnegativity of every term.
Neighborhoods may depend on n. The source formal inverse is normalized by
constant coefficient one on the full domain 0 < r < 1.

## Motivation

This is the all-index nonnegativity conjecture explicitly recorded by OEIS.
The unique-sequence clause supplies source well-definedness, not an additional
external problem.

## Gap

Independent source-fidelity review, formal admission and external problem
settlement remain outside this implementation stage.

## Route

The Lean declaration `A289923LeftLimitNonnegative.result` expresses all these
clauses without a generating-function hypothesis. Its denominator identity
is proved in every degree using the 21-step coefficient relation, and its
positivity conclusion follows by strong induction from a recurrence with
nonnegative forcing coefficients.

## Falsifier

An integer inverse coefficient that stabilizes to a negative value at any
natural index would contradict the target. Failure of the literal floor
denominator to have the claimed index-dependent stabilization would instead
invalidate the connection from the source to the proposed sequence.

## Evidence

The source module and its canonical Blueprint Scribe are
`D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.lean` and
`Blueprint/D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.scribe.cs`.
The audit mirror is
`Reg/D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.lean`.

The strict target is bound to
https://github.com/the-omega-institute/trureturing/issues/29510#issuecomment-6818246365.

## Triage

`theorem`: a universal symbolic conjecture. This classification does not
certify independent review, freeze or external settlement.

## ASSUMED-UNVERIFIED

The identifier search on GitHub found no Lean match for `A289923`.
The pinned source and this bounded search do not establish first-publication
priority, absence of another proof or an exhaustive literature search. No
statistical-independence claim follows from this proof source.
