---
slug: oeis-a382357-valuation-step-permutation
bibkey: oeis2025a382357
doi: null
url: https://oeis.org/A382357
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/ValuationStepPermutation.result
---

# The valuation-step greedy sequence is a permutation

## Problem

OEIS A382357 is the lexicographically earliest sequence of distinct positive
integers whose adjacent 2-adic valuations differ by exactly one. It starts at
1, with offset 1. The supplied source states: “Conjecture: this sequence is a
permutation of the positive integers.”

## Motivation

The target is the permutation conjecture preregistered in issue #15082.
The Lean sequence uses the complete actual history and minimizes the positive
integer itself. Its natural index zero corresponds to OEIS index one.

## Gap

Positivity and injectivity follow from choosing an unused positive integer.
Surjectivity requires an unbounded argument: finite numerical prefixes cannot
exclude a positive integer that is omitted forever.

## Route

The values at valuation level k form the increasing queue 2^k(2r+1).
Every visit takes its least unused entry. A recurrent level covers every value
at its neighboring levels, since an omitted neighbor would bound infinitely
many distinct successor values. Recurrence therefore propagates.

If level zero were not recurrent, every level would have only finitely many
visits, so the heights would eventually exceed any prescribed bound. Count
D_j downward crossings from j to j-1 in a prefix ending above that bound.
The visits to a lower level j are D_j+D_(j+1)+1. At its last exit, greedy
comparison with the unused lower candidate gives
D_(j-1)+D_j >= 4D_(j+1)+1. Hence D_j+2D_(j+1) decreases by at least one
at each level. The total crossings to zero are already bounded once the
height stays above one, contradicting an arbitrarily long descent. Thus
level zero is recurrent, and propagation proves surjectivity.

## Falsifier

A positive integer omitted from the exact history-dependent sequence would
refute the conjecture. A failure of the queue invariant, crossing identity or
last-exit inequality would refute this proof route.

## Evidence

The designated source is
`D5/S3/Combinatorics/Permutation/ValuationStepPermutation.lean`. Its exact claim is
injectivity of a together with occurrence of every positive natural number.
The designated theorem is `result : claim`; verification is scoped to this
module and its dependencies. The supplied numerical checks through level 17
are supporting route evidence, not a proof of the unbounded conclusion.

## Triage

[proved] A382357 is a permutation of the positive integers.

[open] The analogous permutation statements for A382374, using Omega, and
A382376, using omega, remain open. The factor-four last-exit inequality fails
for both; this valuation proof does not establish either statement.

## ASSUMED-UNVERIFIED

The OEIS attribution to Sigrist, source year, conjecture quotation,
preregistration metadata and level-17 numerical check are supplied by the
orchestrator. This seat has no network access and has not independently
checked the live entries, publication priority or exhaustive external
literature. Lean kernel verification does not verify those source facts.
