---
slug: oeis-a393434-factorial-heraclitus
bibkey: oeis2026a393434
doi: null
url: https://oeis.org/A393434
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.result
---

# Every integer occurs in the factorial Heraclitus transform

## Problem

OEIS A393434 starts at a(0) = 0. Each subsequent term is the unused integer
with smallest absolute value at factorial distance k!, k >= 1, from the previous
term. Positive values are preferred when absolute values tie. The source states:
“It is conjectured that every integer appears in this sequence.”

## Motivation

The target is the universal integer-occurrence conjecture preregistered in
issue #15013. The Lean definitions preserve the actual history-dependent greedy
rule, with the integer enumeration 0, 1, -1, 2, -2, and so on.

## Gap

A379719 proves the power-of-2 analogue; the factorial case is stated only as a
conjecture in the supplied source. A finite observed prefix cannot establish
that all integers occur in the unbounded recurrence.

## Route

The initial 25 terms cover [-12,12] without repetition and end at -11. For
k >= 4, a complete interval [-k!/2,k!/2] ending at 1-k!/2 extends to the
corresponding (k+1)! interval. The next term is k!/2+1, followed by consecutive
positive values up to (k+1)!/2, then its negative. The descending negative
magnitudes never have adjacent visited pairs except at the bottom: whenever
at least two units remain, the distance-2 candidate beats the distance-1
candidate. The remaining holes can then be filled in increasing magnitude
with distances 1 or 2, ending at 1-(k+1)!/2. The formal induction records an
existing boundary index and the exact used interval; no formula for the
internal negative order is required. The history length n+1 and its absence
of repetitions identify each boundary index as exactly k!.

## Falsifier

An integer z that never appears in the exact greedy sequence would refute
the conjecture. A failure of the asserted complete-interval boundary or its
terminal value would refute the proposed block invariant.

## Evidence

The designated Lean source is
`D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.lean`, with the literal
`claim : Prop := forall z : Int, exists n : Nat, a n = z` and designated
`result : claim`. Verification is scoped to that module and its dependencies.
The supplied numerical checks for k = 4 through 7 support the proposed route
but are not the proof of the universal statement.

## Triage

[proved] Every integer appears, using the complete-interval block invariant.
The ordering of the positive ascent and the terminal value follow from the
greedy rule, while the descent/fill argument only needs sparsity of visited
negative magnitudes.

[open] A closed expression for the exact order of the negative terms inside
each factorial block is outside the present result.

## ASSUMED-UNVERIFIED

The OEIS attribution, quoted conjecture, power-of-2 comparison and
preregistration metadata are supplied by the orchestrator. This implementation
seat has no network access, so it has not independently checked the live entry,
publication priority or an exhaustive external literature search. Kernel
verification of the Lean theorem does not verify those bibliographic facts.
