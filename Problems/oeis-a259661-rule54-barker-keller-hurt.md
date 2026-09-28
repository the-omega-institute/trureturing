---
slug: oeis-a259661-rule54-barker-keller-hurt
bibkey: price2015rule54rows
doi: null
url: https://oeis.org/A259661
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.result
---

# Barker's, Keller's and Hurt's conjectures for Rule 54

## Problem

OEIS A259661, A118109 and A265225 read the Rule 54 elementary cellular
automaton, started from a single ON cell: its centre column and its rows
`-n..n` as strings of decimal digits, and the total number of ON cells of rows
`0..n`. Their formula fields record

> a(n) = 11*a(n-1) - 11*a(n-2) + 11*a(n-3) - 10*a(n-4) for n>3.
> G.f.: 1 / ((1-x)*(1-10*x)*(1+x^2)).

for A259661,

> a(n) = 10001*a(n-2)-10000*a(n-4) for n>3.
> G.f.: (1+111*x) / ((1-x)*(1+x)*(1-100*x)*(1+100*x)).
> Conjecture: a(n) = floor((10000+1100*(n mod 2))*100^n/9999).

for A118109, and

> a(n) = (n+1)*(2*n -(-1)^n +5)/4.
> a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3) - a(n-4) + a(n-5) for n>4.
> G.f.: (1+3*x) / ((1-x)^3*(1+x)^2).
> a(n) = n + 1 + (n+1) * floor((n+1)/2), conjectured.

for A265225 (Colin Barker 2015 and 2019; Karl V. Keller, Jr. 2021; Wesley Ivan
Hurt 2016). Issue #11145 fixes the reading: every cell of the integers is
updated at every step, the counts of A265225 are cardinalities of the sets of
ON cells, the closed form of Barker is read in the rationals, the floors are
natural-number divisions, and each generating function is stated as the product
of the series with its denominator, which has constant term 1.

## Motivation

The three entries (revisions 55, 53 and 48, 2025-02-16) still label these
statements conjectures. `D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.result`
proves all nine for the literal automaton. Rule 54 is the elementary rule
behind the integrable reversible cellular automaton of Bobenko, Bordemann, Gunn
and Pinkall, a standard model of interacting integrable lattice dynamics.

## Gap

Issue #11145 preregisters the proof route and the literature check: the entries
and their links give no proof (MathWorld's "Rule 54" page states the base-2 row
values of A118108 without proof; Munarini 2021, linked from A265225, cites the
sequence only for a power-series identity and does not treat the automaton), and
none of the three entries appears in the statement sets or results of
`epoch-research/LeanOpenProblems`, `epoch-research/LeanOpenProblems-results`,
`google-deepmind/alphaproof-nexus-results` or `google-deepmind/formal-conjectures`,
which do contain the Rule 167 entry A267581. `not-found-in-searched-scope`.

## Route

1. By induction on `n`, the cell at `x` of row `n` is ON exactly when
   `|x| ≤ n` and `x ≡ n (mod 4)` for even `n`, or `x ≢ n + 1 (mod 4)` for
   odd `n`.
2. The centre cell of row `k` is ON exactly when `k ≡ 0, 1 (mod 4)`; with
   `a(n+1) = 10 a(n) + c(n+1)` this gives the A259661 recurrence.
3. Digit `j + 4` of row `n + 2` equals digit `j` of row `n`, and the first four
   digits of row `n + 2` are `1, 0, 0, 0` (even `n`) or `1, 1, 1, 0` (odd `n`).
   In base 10 this gives `9999 a(n) = 10000·100^n − 1` or `11100·100^n − 111`,
   hence Keller's floor and Barker's recurrence for A118109.
4. With base 1 the same shift counts the ON cells of row `k`: `k/2 + 1` for even
   `k` and `3(k + 1)/2` for odd `k`. Summing gives Hurt's formula, which equals
   Barker's closed form and satisfies his recurrence.
5. The generating functions follow by comparing coefficients.

## Falsifier

The proof would fail if some row differed from the pattern of step 1, or if the
digit shift of step 3 failed for some `n`.

## Evidence

Exact integer computation (issue #11145): simulating the automaton with every
cell updated reproduces all terms of the three b-files (1000, 500 and 1000);
all nine statements hold on those ranges; the controls (`−10 → −9` in the
A259661 recurrence, `10000 → 9999` in the A118109 recurrence, `1100 → 1101` in
Keller's floor, `+5 → +6` in Barker's closed form) fail at 996, 496, 249 and
1000 indices.

The canonical source is
`D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows.lean`. Its public
declarations are `rule54`, `cell`, `centreColumn`, `binaryRow`, `totalOn`,
`claim`, and `result`. The frozen module state has statement identity
`sha256:7e9c025966930cddb6c7e79ffc9d6f515cfa5216bd23cd9b9f729ddb2956544a`.
The result declaration has statement identity
`sha256:899a419dfe1341f684b52696e4d97f1b14b87769634d7b721092d908cecc9c42`.
The Freeze event is
`sha256:7f4b49a76fef8b88cbe601c2fe3019c2343b7572928e23860731e815d79628ec`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjectures (OEIS formula fields), preregistered in
issue #11145 before any repository Lean. `theorem`; resolution `proved`. The
public theorem has `proof_shape: content`: the row invariant of step 1 and the
row shift of step 3 are new propositions on its live path. Admission basis
`open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
