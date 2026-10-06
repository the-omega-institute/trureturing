---
slug: oeis-a266614-rule41-barker
bibkey: price2016rule41oncells
doi: null
url: https://oeis.org/A266614
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.result
---

# Barker's conjectures for the ON cells of Rule 41

## Problem

OEIS A266614 counts the ON cells among the cells `-n, …, n` of row `n` of the
Rule 41 elementary cellular automaton started from a single ON cell. Its
formula field records

> Conjectures from _Colin Barker_, Jan 02 2016 and Apr 18 2019: (Start)
> a(n) = a(n-2)+a(n-4)-a(n-6) for n>5.
> G.f.: (1+x^2+3*x^3-2*x^4+5*x^5) / ((1-x)^2*(1+x)^2*(1+x^2)).
> (End)

Issue #13157 fixes the reading: every cell of the integers is updated at every
step, the recurrence is asserted for `n > 5` in the integers, and the
generating function is stated as the product of the series with its
denominator, which has constant term 1.

## Motivation

A266614 (revision 18, 2025-02-16) still labels both statements conjectures.
`D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.result` proves
both for the literal automaton.

## Gap

Issue #13157 preregisters the proof route and the literature check: the entry
and its references (MathWorld, *A New Kind of Science* p. 55) give no proof,
and the entry does not appear in `epoch-research/LeanOpenProblems`,
`google-deepmind/alphaproof-nexus-results`, `google-deepmind/formal-conjectures`,
`provables/sequencelib` or `ai4reason/oeis-atp-benchmark`.
`not-found-in-searched-scope`.

## Route

1. By induction on `n`, the background of row `n` is OFF for even `n` and ON
   for odd `n`, and row `n` differs from it exactly at `{n}`,
   `{n − 2, n − 1, n}`, `{n − 2, n}` or `{n − 4, n − 3, n − 1, n}` according as
   `n ≡ 0, 1, 2, 3 (mod 4)`: rule 41 sends `lcr` to 1 exactly for `000`, `011`
   and `101`.
2. All the exceptional cells lie in the window, so
   `a(4k) = 1`, `a(4k + 1) = 8k`, `a(4k + 2) = 2` and `a(4k + 3) = 8k + 3`.
3. The recurrence follows phase by phase, and the generating function by
   comparing coefficients: from `x^6` on the coefficients of the product with
   `1 − x² − x⁴ + x⁶` vanish by the recurrence, and the first six come from the
   values `1, 0, 2, 3, 1, 8`.

## Falsifier

The proof would fail if some row differed from the pattern of step 1.

## Evidence

Exact computation: simulating the automaton with every cell updated
reproduces the entry's data; for `n ≤ 2000` the pattern of step 1 holds on the
whole simulated line, and both formulas hold.

The canonical source is
`D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount.lean`. Its
public declarations are `rule41`, `onCount`, `claim`, and `result`; the rows are
the frozen single-seed evolution `row` of
`D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation` applied to `rule41`.
The frozen module state has statement identity
`sha256:173762a05135868b08adbc0dbdc42fd06e7dd55d9f87579b15a4950087ae0b4d`.
The result declaration has statement identity
`sha256:89ddd5195aa776156bfbb4be0346c953299acad01aaf2faf92f6ec3e7e1e374d`.
The Freeze event is
`sha256:0efea5306cd5c4212f6a5b683853c72b5fb55d215143f30e3a836c4858d0a5a9`.
Its project-level frozen prerequisite is the Freeze event of
`D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation`
(`sha256:0ac64d9044734ddcb1c55bdba77086423f83617cfff4772da4a64279f49770ee`).
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 external named conjectures (OEIS formula fields), preregistered in
issue #13157 before any Lean. `theorem`; resolution `proved`. The public
theorem has `proof_shape: content`: the four-phase row invariant of step 1 and
the counts of step 2 are new propositions on its live path. Admission basis
`open-problem-resolution`; utility `none`.

Effect on the entry's other statements: the two formulas are all the
conjectures the entry records, and both are proved, so none remains open. The
counts of step 2 (proved) also give the closed form `a(n) = 1, 2n − 2, 2, 2n − 3`
for `n ≡ 0, 1, 2, 3 (mod 4)`, which the entry does not state.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
