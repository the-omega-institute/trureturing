---
slug: oeis-a266285-rule13-barker-zizka
bibkey: price2015rule13oncells
doi: null
url: https://oeis.org/A266285
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.result
---

# Barker's and Zizka's conjectures for the ON cells of Rule 13

## Problem

OEIS A266285 counts the ON cells among the cells `-n, …, n` of row `n` of the
Rule 13 elementary cellular automaton started from a single ON cell. Its
formula field records

> Conjectures from _Colin Barker_, Dec 28 2015 and Apr 14 2019: (Start)
> a(n) = ((-1)^n*(3-2*n)+4*n+1)/4.
> a(n) = 2*a(n-2)-a(n-4) for n>3.
> G.f.: (1+x+2*x^3) / ((1-x)^2*(1+x)^2). (End)
> Conjecture from _Ctibor O. Zizka_, Mar 11 2025: (Start)
> a(2*n) = n + 1.
> a(2*n + 1) = 3*n + 1.(End)

Issue #13151 fixes the reading: every cell of the integers is updated at every
step, the closed form is read in the rationals, the recurrence is asserted for
`n > 3` in the integers, and the generating function is stated as the product
of the series with its denominator, which has constant term 1.

## Motivation

A266285 (revision 28, 2025-03-12) still labels all of these statements
conjectures. `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.result`
proves all five for the literal automaton.

## Gap

Issue #13151 preregisters the proof route and the literature check: the entry
and its references (MathWorld, *A New Kind of Science* p. 55) give no proof;
the entry does not appear in the statement sets or results of
`epoch-research/LeanOpenProblems`, `google-deepmind/alphaproof-nexus-results`
or `google-deepmind/formal-conjectures`; `provables/sequencelib` and
`ai4reason/oeis-atp-benchmark` contain only synthesized programs checked
against initial terms, not related to the automaton.

The five formulas are implied by published work: H. Fukś, *Solvable Cellular
Automata* (Springer, 2023), Appendix B, gives the explicit solution of Rule 13
for an arbitrary initial configuration
(`Library/StatisticalMechanics/fuks2023solvable.md`). Specialized to the single
ON seed it yields the row pattern of the Route below, and the counts follow.

## Route

1. By induction on `n`, row `2k` is ON exactly at the even `x` with
   `0 ≤ x ≤ 2k`, and row `2k + 1` is OFF exactly at the odd `x` with
   `-1 ≤ x ≤ 2k + 1`: rule 13 sends `lcr` to 1 exactly when `l = 0` and
   either `c = 1` or `r = 0`.
2. Hence the window of row `2k` holds `k + 1` ON cells, and the window of row
   `2k + 1`, which has `4k + 3` cells, holds `k + 2` OFF cells, so
   `a(2k + 1) = 3k + 1`.
3. Barker's closed form follows by parity, his recurrence by the parity of
   `n − 4`, and his generating function by comparing coefficients: from `x^4`
   on the coefficients of the product with `1 − 2x² + x⁴` vanish by the
   recurrence, and the first four come from the values `1, 1, 2, 4`.

## Falsifier

The proof would fail if some row differed from the pattern of step 1.

## Evidence

Exact computation: simulating the automaton with every cell updated
reproduces the entry's data; for `n ≤ 2000` the row pattern of step 1 holds on
the cells `-n - 1, …, n + 1` and Barker's closed form holds.

The canonical source is
`D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount.lean`. Its
public declarations are `rule13`, `onCount`, `claim`, and `result`; the rows are
the frozen single-seed evolution `row` of
`D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation` applied to `rule13`.
The frozen module state has statement identity
`sha256:8fa51962788beeef2914c92f074b51a4c89e9364c7796bda0e3329a77abe0ef4`.
The result declaration has statement identity
`sha256:9743657443c83e35aac3d02899451b633a63d726684c1bf56a646236c5d18677`.
The Freeze event is
`sha256:bd8a496acc5c5f11bfd4850d28e6bf2bb6904b839154d13a472cd88285c9ae82`.
Its project-level frozen prerequisite is the Freeze event of
`D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation`
(`sha256:0ac64d9044734ddcb1c55bdba77086423f83617cfff4772da4a64279f49770ee`).
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 external named conjectures (OEIS formula fields), preregistered in
issue #13151 before any Lean. `theorem`; resolution `proved`. Literature status:
`literature-attested` by specialization of the Rule 13 solution in Fukś (2023),
Appendix B; the module is a kernel-checked derivation of a literature-implied
result, not a first resolution. The public
theorem has `proof_shape: content`: the row invariant of step 1 and the counts
of step 2 are new propositions on its live path. Admission basis
`open-problem-resolution`; utility `none`.

Effect on the entry's other statements: the five formulas are all the
conjectures the entry records, and all five are proved, so none remains open.
The row pattern of step 1 (proved) determines every other reading of the same
rows, for example the number of OFF cells in the window, `3n / 2` for even `n` and
`(n + 3) / 2` for odd `n`, which follows from the proved counts because the
window has `2n + 1` cells (not formalized here).

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
