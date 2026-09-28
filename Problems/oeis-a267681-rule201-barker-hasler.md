---
slug: oeis-a267681-rule201-barker-hasler
bibkey: price2016rule201rows
doi: null
url: https://oeis.org/A267681
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.result
---

# Barker's and Hasler's conjectures for the rows of Rule 201

## Problem

OEIS A267681 and A267680 read row `n` of the Rule 201 elementary cellular
automaton, started from a single ON cell, on the cells `-n, …, n`: in base 2
(A267681) and as a string of decimal digits (A267680). Their formula fields
record

> a(n) = 5*a(n-1)-20*a(n-3)+16*a(n-4) for n>4.
> G.f.: (1-5*x+21*x^2+14*x^3-40*x^4) / ((1-x)*(1-2*x)*(1+2*x)*(1-4*x)).

> Conjecture: a(n) = 2*4^n - (n%2*2 + [n]*5)*2^(n-1) - 1, where [n] = 1 iff
> n > 0; n%2 = 1 iff n is odd. - _M. F. Hasler_, Jul 28 2018

for A267681 (the first two by Colin Barker, Jan 19 2016), and

> a(n) = 101*a(n-1)-10100*a(n-3)+10000*a(n-4) for n>4.
> G.f.: (1-101*x+10101*x^2+89910*x^3-101000*x^4) / ((1-x)*(1-10*x)*(1+10*x)*(1-100*x)).

for A267680 (Colin Barker, Jan 19 2016 and Apr 20 2019). Issue #11102 fixes
the reading: every cell of the integers is updated at every step, the
recurrences are asserted for `n > 4`, and each generating function is stated
as the product of the series with its denominator, which has constant term 1.

## Motivation

A267681 (revision 30, 2025-02-16) still labels these statements conjectures,
and its history records that a claim of their correctness was removed in 2022.
`D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.result` proves all
five for the literal automaton. Rule 201 is the local update rule of the
Floquet-PXP cellular automaton (Wilkinson, Klobas, Prosen and Garrahan 2020).

## Gap

Issue #11102 preregisters the proof route and the literature check: the
entries and their links (MathWorld, *A New Kind of Science* p. 55, the OEIS
cellular automata indexes) give no proof, and neither entry appears in the
statement sets or results of `epoch-research/LeanOpenProblems`,
`epoch-research/LeanOpenProblems-results`,
`google-deepmind/alphaproof-nexus-results` or
`google-deepmind/formal-conjectures`, which do contain the Rule 167 entry
A267581. `not-found-in-searched-scope`.

## Route

1. By induction on `n`, for `n ≥ 1` the cell at `x` of row `n` is ON exactly
   when `|x| ≥ 2`, or `x = 0` and `n` is even.
2. Hence the window of row `n ≥ 1` in base `b` is
   `Σ_{j < 2n+1} b^j − b^{n+1} − b^{n−1} − [n odd] b^n`.
3. With `(b − 1) Σ_{j<k} b^j = b^k − 1` and `2 [n odd] = 1 − (−1)^n`, for
   every base `b ≥ 1` twice `(b − 1)` times the window is a combination of
   `b^{2n}`, `b^n`, `(−b)^n` and `1`, each annihilated by `(1 − x)(1 − bx)(1 + bx)(1 − b²x)`; this
   gives both recurrences, and for `b = 2` step 2 is Hasler's formula.
4. The generating functions follow by comparing coefficients: from `x^5` on
   they vanish by the recurrence, and the first five come from the values
   `1, 0, 21, 99, 471` and `1, 0, 10101, 1100011, 111010111`.

## Falsifier

The proof would fail if some row `n ≥ 1` differed from the pattern of step 1,
or if the combination of step 3 were not annihilated by the characteristic
polynomial for some `n > 4`.

## Evidence

Exact integer computation (issue #11102): simulating the automaton with every
cell updated reproduces all 1001 terms of both b-files; Hasler's formula and
both recurrences hold for `n ≤ 1000`; replacing the constant `−1` of Hasler's
formula by `−2`, or `10000` by `9999` in the decimal-digit recurrence, fails
at 1001 and 995 indices.

The canonical source is
`D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows.lean`. Its public
declarations are `rule201`, `cell`, `windowValue`, `decimalRepresentation`,
`binaryRepresentation`, `claim`, and `result`. The frozen module state has
statement identity
`sha256:5ce9a4203589a1076c7f95493127548c3819869402c7d1391578d8173a379139`.
The result declaration has statement identity
`sha256:a1c39ab3c34161d5b82f11d85866b85fc240c8c90e040cb7d9a3fbbdf70bedd4`.
The Freeze event is
`sha256:8cc996728977659630204dcbd5a216c8530ef01186be9493a75d25e1a80cd51e`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjectures (OEIS formula fields), preregistered in
issue #11102 before any Lean. `theorem`; resolution `proved`. The public
theorem has `proof_shape: content`: the row invariant of step 1 and the window
evaluation of step 2 are new propositions on its live path. Admission basis
`open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
