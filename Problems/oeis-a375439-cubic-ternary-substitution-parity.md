---
slug: oeis-a375439-cubic-ternary-substitution-parity
bibkey: hanna2024a375439
doi: null
url: https://oeis.org/A375439
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity
---

# Parity of the A375439 coefficients

## Problem

OEIS A375439 (Paul D. Hanna, Aug 21 2024) supplies the following statements,
copied from the claim in `Library/Arith/hanna2024a375439.md`:

NAME "Expansion of g.f. A(x) satisfying A(x) = x + x^2 + (2*A(x)^3 + A(x^3))/3."

COMMENT "Conjecture: a(n) is odd iff n is in A038754, which consists of numbers of the form 3^k and 2*3^k."

The sequence starts at index one; the integer formal generating series is
normalized by its zero constant coefficient.

## Motivation

This is a first-tier recent OEIS conjecture selected in the implementation
brief. KPI = open problems resolved. The target is the full parity assertion
for every positive index, with no finite search bound.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-08 and searching for the identifiers on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
repeat that search. The report is limited to those sources, not an exhaustive
literature or publication-priority claim.

## Route

Frobenius modulo three gives `cube_congr_subst_three`: for any integer formal
series B, B^3 and B(x^3) agree coefficientwise modulo three. Consequently
`numerator_dvd` proves that every coefficient of 2B^3+B(x^3) is divisible by
three, so the division in the defining transformation is exact.

For series with zero constant coefficient, degree contraction improves
agreement below degree d to agreement below degree d+1. Stabilized
approximations construct the integer series and prove `generating_equation`;
induction on coefficient agreement proves `generating_unique` among integer
series with zero constant coefficient satisfying that equation.

The coefficient equation reduces modulo two to
`a(n) ≡ [n=1] + [n=2] + [3∣n]·a(n/3)`. Strong induction on the index gives the
two unbounded support families 3^k and 2·3^k in `hanna_conjecture`. The module
has no D5 import, uses Mathlib only, and declares generality G.

## Falsifier

A positive index n for which a(n) is odd but n is in neither support family,
or for which n is in either family but a(n) is even, would contradict the
assertion. The orchestrator's exact finite check is supporting evidence only;
it does not establish the unbounded theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.lean`.
- Main theorem: `hanna_conjecture`, for every natural n with `1 ≤ n`.
- Companions: `generating_equation`, `generating_unique`, and
  `cube_congr_subst_three`. The last is a bind-only Mathlib wrapper consumed
  through `numerator_dvd` on the live path to the equation and parity theorem.
- The implementation seat's axiom report recorded std3 for all four public
  theorems: `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. The formal proof closes the universal parity assertion recorded by
OEIS and supplies the integer generating series, its equation, and uniqueness.

## ASSUMED-UNVERIFIED

The quotations, author, and date were supplied by the orchestrator; this seat
copied the quotation text from the Library note rather than reading OEIS.
The OEIS entry and revision history were read by the search seat on
2026-09-08, not by this seat. The reported literature search covered OEIS and
identifier searches on arXiv, MathOverflow, and GitHub; it did not establish
exhaustive coverage or first-publication priority. Source-to-Lean fidelity is
not a kernel-checked fact. This offline seat did not rerun the orchestrator's
finite checks or the implementation seat's axiom report.
