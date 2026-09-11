---
slug: oeis-a374570-catalan-composition-square-parity
bibkey: hanna2024a374570
doi: null
url: https://oeis.org/A374570
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity
---

# Parity of the Catalan-composition series A374570

## Problem

OEIS A374570 (Paul D. Hanna, Jul 11 2024), quoted verbatim from
`Library/Arith/hanna2024a374570.md`:

NAME:
> Expansion of g.f. A(x) satisfying A(x)^2 = A( A(x)*C(x) ), where C(x) = x + C(x)^2 is the Catalan function (A000108).

COMMENT:
> Conjecture: for n > 1, a(n) is odd iff n = 2^k + 1 for k >= 0.

The normalization is `A(0) = 0`, `a(1) = 1`, and `C(0) = 0`.

## Motivation

This is a first-tier recent OEIS conjecture. The KPI is open problems resolved,
not modules, seats, or finite checks. The target is the assertion for every
natural index `n > 1`.

## Gap

The supplied search reports no proof found: the search seat read the OEIS entry
and revision history on 2026-09-08 and searched the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network and did not repeat
those searches. This bounded search is not an exhaustive literature census.

## Route

Set `C = X * catalanUnit`, using Mathlib's `PowerSeries.Catalan`;
`catalan_equation` and `catalan_unique` identify the normalized Catalan function.
Construct the integer solution `A = X * B` by degree-contracting stabilization
of `B -> catalanUnit * B(X^2 * B * catalanUnit)`. The results
`generating_equation` and `generating_unique` establish existence and uniqueness
of the normalized solution to the exact functional equation.

Over `ZMod 2`, the live cancellation chain is
`A(X^2) = A(A*C)` implies `A*C = X^2` implies `A = X*(1+C)`.
Outer cancellation uses Mathlib's compositional-inverse API. The Catalan
identity gives `C*(1+C) = X`; writing `C` as `X` times a unit justifies the
remaining cancellation. Strong induction on the characteristic-two
coefficient contraction gives `binary_catalan`: the support of `C` consists
exactly of powers of two. Hence, for `n > 1`, `a(n)` is odd if and only if
`n - 1 = 2^k`, equivalently `n = 2^k + 1`, as stated by `hanna_conjecture`.
The module has no D5 import and has generality `G`.

## Falsifier

A counterexample index `n > 1` at which `Odd (a n)` disagrees with
`exists k : Nat, n = 2^k + 1` would contradict the assertion. The orchestrator's
exact numerical check is supporting evidence only; no finite bound proves
this universally quantified statement.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `catalan_equation`, `catalan_unique`, `generating_equation`,
  `generating_unique`, and `binary_catalan`.
- Axioms: `std3` (`propext`, `Classical.choice`, `Quot.sound`), as reported for
  each public theorem by the implementation seat.

## Triage

`theorem`. The formal proof closes the universal assertion recorded by OEIS
for the normalized integer generating series.

## ASSUMED-UNVERIFIED

The OEIS quotations and attribution were supplied by the orchestrator and
copied from the Library note. The OEIS revision history was read by the search
seat, not this seat. The literature scope was the OEIS entry and history plus
identifier searches on arXiv, MathOverflow, and GitHub, as reported above;
this seat had no network. First-publication priority and the source-to-Lean
identification are not kernel-checked facts. The std3 report and numerical
check were supplied evidence, not checks rerun by Stage B.
