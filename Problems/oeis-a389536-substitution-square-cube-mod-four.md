---
slug: oeis-a389536-substitution-square-cube-mod-four
bibkey: hanna2025a389536
doi: null
url: https://oeis.org/A389536
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour
---

# The A389536 square-cube substitution conjecture

## Problem

OEIS A389536, Paul D. Hanna, Oct 28 2025. The following verbatim NAME and
COMMENT quotations are recorded in `Library/Arith/hanna2025a389536.md`:

NAME:

> G.f. A(x) satisfies: A(x) = A(x^2 + 2*x^3) / x.

COMMENT:

> Conjecture: for n > 1, a(n) == 2 (mod 4) when n = 2^k + 1 (for some k >= 0) otherwise a(n) is divisible by 4.

## Motivation

This is a first-tier recent OEIS conjecture. The KPI is open problems resolved:
the target is the complete assertion for every index greater than one.

## Gap

The supplied search-seat report found no proof in the OEIS entry and revision
history read on 2026-09-08, or in identifier searches on arXiv, MathOverflow,
and GitHub. This Stage-B seat had no network access and did not repeat those
searches. No exhaustive literature search or priority claim follows from this
bounded negative result.

## Route

The integer sequence is defined by a well-founded coefficient recursion, with
`a(0) = 0` and `a(1) = 1`. The series is PROVED to satisfy the OEIS equation,
written without division as `X * generatingSeries = generatingSeries.subst
(X ^ 2 + 2 * X ^ 3)`, by `generating_equation`. The theorem
`generating_unique` proves it is the unique zero-constant solution with
`a(1) = 1`; the normalization is not forced by the equation alone.

Extracting coefficient `n+1` and expanding `(X^2 + 2*X^3)^k` proves
`coeff_recurrence`: for `n >= 2`,
`a(n) = sum_k a(k) * 2^(n+1-2k) * C(k, n+1-2k)`.
Here `0 <= k < n`, and only `2k <= n+1` contributes; the Lean sum uses
`Fin n` and an explicit degree guard, so natural subtraction cannot introduce
spurious terms. Modulo 4 only the exponents 0 and 1 survive. This gives
`a(2m-1) == a(m) (mod 4)` for `m >= 2` and
`a(2m) == 2m*a(m) (mod 4)` for `m >= 1`. Strong induction proves `a(n)` even
for `n >= 2`, then classifies all remainders: index 2 has remainder 2, even
indices at least 4 have remainder 0, and the odd contraction preserves exactly
the indices `2^k+1`.

There are no D5 imports or direct frozen prerequisites. The imports are
`Mathlib.RingTheory.PowerSeries.Substitution` and
`Mathlib.Algebra.BigOperators.ModEq`; the module has generality `G`.

## Falsifier

An index `n > 1` with `n = 2^k+1` but `a(n) % 4 != 2`, or with no such
natural `k` but `a(n) % 4 != 0`, would falsify the assertion. The orchestrator's
exact numerical check is supporting evidence only; it does not replace the
unbounded proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `coeff_recurrence`,
  and `a_even`.
- Public definitions: `a` and `generatingSeries`.
- Axioms: std3, exactly `propext`, `Classical.choice`, and `Quot.sound` for
  each public theorem, as recorded by the implementation seat's Lean run.
- The Scribe resolution claim is attached only to `hanna_conjecture`.

## Triage

`theorem`. The formal proof closes the complete normalized OEIS assertion,
including both remainder equivalences for every natural `n > 1`.

## ASSUMED-UNVERIFIED

The OEIS quotations and attribution were supplied by the orchestrator and
copied from the Library note. The OEIS entry and revision history were read
by the search seat on 2026-09-08, not by this Stage-B seat. The literature
scope was the entry and its history plus identifier searches on arXiv,
MathOverflow, and GitHub; no independent proof was found in that scope.
This seat had no network access. Source-to-Lean identification, literature
completeness, and first-publication priority are not kernel-checked facts.
