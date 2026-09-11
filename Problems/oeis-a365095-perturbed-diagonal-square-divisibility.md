---
slug: oeis-a365095-perturbed-diagonal-square-divisibility
bibkey: hanna2023a365095
doi: null
url: https://oeis.org/A365095
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility
---

# Square divisibility of the A365095 perturbed diagonal

## Problem

OEIS A365095, Paul D. Hanna, Sep 03 2023. NAME (the defining formula (1)):

> Expansion of g.f. A(x) satisfying [x^(n-1)] (1 + (n-1)*x*A(x)^2)^n / A(x)^n = 0 for n > 1.

FORMULA (2), the target:

> [x^(n-1)] (1 + (k*n-1)*x*A(x)^2)^n / A(x)^n is divisible by n^2 for n > 0 and all integer k (conjecture).

The normalization is `A(0) = 1`; the parameter ranges over all integers.

## Motivation

This first-tier OEIS conjecture is from the 2023 entry. KPI = open problems
resolved. The target is square divisibility for every positive natural index
and every integer perturbation parameter.

## Gap

No proof was found in the supplied search: the search seat read the OEIS entry
and revision history on 2026-09-09 and searched the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not repeat
those searches. This is a bounded literature-search report, not a priority proof.

## Route

The escape content is the integral triangular construction together with the
perturbation congruence `(B + n·C)^n ≡ B^n (mod n²)`. Set
`B = 1 + (n−1)·x·A²`. Moving from the defining `k = 1` to any integer `k`
replaces the base by `B + n·(k−1)·x·A²`. Every binomial term containing two
or more perturbation factors carries `n²`; the single-factor term also carries
`n²` because its binomial coefficient is `n`. The remaining `B^n` term,
after multiplication by `A^{-n}`, has degree-(n−1) coefficient zero by the
entry's defining formula (1) for `n > 1`. At `n = 1`, the divisor is one.

The construction is the other half. In degree `m = n−1`, the new coefficient
has multiplier `−(m+1) = −n`, which is not an integer unit. Differentiation
proves that `m+1` divides the residual, so the triangular solve uses exact
integer division. The inverse-difference identity proves contraction and
stabilization; the fixed point satisfies formula (1) and is unique. This
corrects the unit-multiplier wording in the supplied route. Over `PowerSeries ℤ`,
`A^{-n}` is `invOfUnit A 1 ^ n`; no Laurent machinery is used.

The quantifier over `k : ℤ` is the point of the lane. The delivered theorem is
`hanna_conjecture (k : ℤ) (n : ℕ) (hn : 0 < n) :
(n : ℤ) ^ 2 ∣ perturbedDiagonal k n`, including negative and zero `k`.
The module imports only Mathlib, with no D5 import; its generality is G.

## Falsifier

A positive index `n` and an integer `k` for which `n²` fails to divide the
specified coefficient would falsify formula (2). The orchestrator's exact
check is supporting evidence only; no finite check replaces the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/PerturbedDiagonalSquareDivisibility.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`; definition: `perturbedDiagonal`.
- All six public declarations have std3 axioms: `[propext, Classical.choice, Quot.sound]`,
  as reported by the implementation seat's single-file Lean check (exit 0).
- The orchestrator reported successful build, Lean-report, and emit checks before
  these Scribe edits. Stage B did not execute those commands.

## Triage

`theorem`. The formal proof closes formula (2) for every integer `k` and positive `n`.

## ASSUMED-UNVERIFIED

The verbatim NAME and FORMULA (2) quotations were supplied by the orchestrator.
`Library/ArithSums/hanna2023a365095.md` records NAME verbatim in its claim and
restates formula (2) with a leading “Conjecture:” rather than its terminal
“(conjecture).”; the terminal wording above follows the supplied OEIS quotation.
The search seat, not this seat, read the OEIS revision history on 2026-09-09.
The literature scope was the OEIS entry/history and identifier searches on
arXiv, MathOverflow, and GitHub; it does not establish an exhaustive literature
review or first-publication priority. Source-to-Lean identification and the
orchestrator's exact check are not independently verified by this offline seat.
