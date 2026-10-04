---
slug: oeis-a266981-rule79-barker-zizka
bibkey: price2016rule79oncells
doi: null
url: https://oeis.org/A266981
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.result
---

# Barker's and Zizka's conjectures for the ON cells of Rule 79

## Problem

OEIS A266981 counts the ON cells among the cells `-n, …, n` of row `n` of the
Rule 79 elementary cellular automaton started from a single ON cell. Its
formula field records

> Conjectures from _Colin Barker_, Jan 08 2016 and Apr 19 2019: (Start)
> a(n) = (3+(-1)^n-2*(-2+(-1)^n)*n)/4.
> a(n) = 2*a(n-2)-a(n-4) for n>3.
> G.f.: (1+2*x+x^3) / ((1-x)^2*(1+x)^2). (End)
> Conjecture from _Ctibor O. Zizka_, Mar 11 2025: (Start)
> a(2*n) = n + 1.
> a(2*n + 1) = 3*n + 2.(End)

Issue #13155 fixes the reading: every cell of the integers is updated at every
step, the closed form is read in the rationals, the recurrence is asserted for
`n > 3` in the integers, and the generating function is stated as the product
of the series with its denominator, which has constant term 1.

## Motivation

A266981 (revision 33, 2025-03-12) still labels all of these statements
conjectures. `D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.result`
proves all five for the literal automaton.

## Gap

Issue #13155 preregisters the proof route and the literature check: the entry
and its references (MathWorld, *A New Kind of Science* p. 55) give no proof;
the entry does not appear in the statement sets or results of
`epoch-research/LeanOpenProblems`, `google-deepmind/alphaproof-nexus-results`
or `google-deepmind/formal-conjectures`; `provables/sequencelib` and
`ai4reason/oeis-atp-benchmark` contain only synthesized programs checked
against initial terms, not related to the automaton.
`not-found-in-searched-scope`.

## Route

1. By induction on `n`, row `2k` is ON exactly at the even `x` with
   `0 ≤ x ≤ 2k`, and row `2k + 1` is OFF exactly at the odd `x` with
   `1 ≤ x ≤ 2k + 1`: rule 79 sends `lcr` to 1 exactly when `l = 0`, or
   `c = 1` and `r = 0`.
2. Hence the window of row `2k` holds `k + 1` ON cells, and the window of row
   `2k + 1`, which has `4k + 3` cells, holds `k + 1` OFF cells, so
   `a(2k + 1) = 3k + 2`.
3. Barker's closed form follows by parity, his recurrence by the parity of
   `n − 4`, and his generating function by comparing coefficients: from `x^4`
   on the coefficients of the product with `1 − 2x² + x⁴` vanish by the
   recurrence, and the first four come from the values `1, 2, 2, 5`.

## Falsifier

The proof would fail if some row differed from the pattern of step 1.

## Evidence

Exact computation: simulating the automaton with every cell updated
reproduces the entry's data; for `n ≤ 2000` the row pattern of step 1 holds on
the cells `-n - 1, …, n + 1` and Barker's closed form holds.

The canonical source is
`D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount.lean`. Its
public declarations are `rule79`, `onCount`, `claim`, and `result`; the rows are
the frozen single-seed evolution `row` of
`D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation` applied to `rule79`.
The frozen module state has statement identity
`sha256:e4501045d3868250bcf5634b00c3838eea74279c76c6a3f0b651ea36c4744b30`.
The result declaration has statement identity
`sha256:3b8189feb62b48a5a6259b878259df3e8acd8bae4de8a739e64af3ce10172499`.
The Freeze event is
`sha256:0c0b73ab00743d3d0790bf9e4bdf76a694e9b94ffc9b39f2ade4198f46f48806`.
Its project-level frozen prerequisite is the Freeze event of
`D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation`
(`sha256:0ac64d9044734ddcb1c55bdba77086423f83617cfff4772da4a64279f49770ee`).
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 external named conjectures (OEIS formula fields), preregistered in
issue #13155 before any Lean. `theorem`; resolution `proved`. The public
theorem has `proof_shape: content`: the row invariant of step 1 and the counts
of step 2 are new propositions on its live path. Admission basis
`open-problem-resolution`; utility `none`.

Effect on the entry's other statements: the five formulas are all the
conjectures the entry records, and all five are proved, so none remains open.
The row pattern of step 1 (proved) determines every other reading of the same
rows, for example the number of OFF cells in the window, `3n / 2` for even `n` and
`(n + 1) / 2` for odd `n`, which follows from the proved counts because the
window has `2n + 1` cells (not formalized here).

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
