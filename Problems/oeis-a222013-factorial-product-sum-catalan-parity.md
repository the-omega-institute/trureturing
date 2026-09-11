---
slug: oeis-a222013-factorial-product-sum-catalan-parity
bibkey: hanna2024a222013
doi: null
url: https://oeis.org/A222013
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity
---

# Parity of the A222013 factorial product sum coefficients

## Problem

Paul D. Hanna created OEIS A222013 on Feb 04 2013; the parity conjecture
is dated Dec 06 2024. These quotations are copied verbatim from
`Library/Recurrence/hanna2024a222013.md`.

NAME:

> G.f. satisfies: A(x) = Sum_{n>=0} n! * x^n * A(x)^(n*(n+1)/2) / Product_{k=1..n} (1 + k*x*A(x)^k).

COMMENT:

> Conjecture: a(n) is odd iff n = 2^k - 1 for some k >= 0. - _Paul D. Hanna_, Dec 06 2024

The infinite sum is formalised with the exact finite window at each coefficient,
as stated in Route and quoted in Lean syntax in Evidence.

## Motivation

This is a first-tier OEIS conjecture from a 2013 entry, with the conjecture
dated 2024. KPI = open problems resolved. The target theorem covers every
natural index, including zero.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and performing identifier searches on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network access and did not
independently repeat those searches. This bounded search does not establish
exhaustive literature coverage or publication priority.

## Route

`term r F` is r! times X^r times F^{r(r+1)/2} times
`invOfUnit` of the product of `(1 + k*X*F^k)` for k from 1 through r,
with unit argument 1. Each denominator has constant coefficient one, so
this is formal division by a unit. `term_coeff_eq_zero` proves that index r
contributes nothing at degree N < r. Thus `generating_equation` states
A(0) = 1 and, for every N,
`coeff N A = sum (r in range (N+1)) (coeff N (term r A))`.
Mathlib has no infinite sums of formal series; this exact coefficientwise
finite-window statement is the honesty boundary, with no analytic convergence
or separate infinite-sum operator asserted.

Degree contraction constructs the integer solution by stabilised iteration.
`generating_unique` covers every integer series B with constant coefficient
one satisfying the same family of coefficient equations.
Over `ZMod 2`, every summand with r >= 2 vanishes because 2 divides r!.
For C equal to the coefficientwise reduction of A, `mod_two_equation` gives
`C = 1 + X*C^2` after multiplication by the remaining denominator unit.

The frozen `CatalanCompositionSquareParity.catalan_equation` supplies
`K = X + K^2`. A local uniqueness proof over `ZMod 2` cancels the unit
`1 - F - G` between two zero-constant solutions. This gives
`mod_two_identity`: X times C equals the reduction of K.
The frozen `binary_catalan` support at {2^k} then gives
`hanna_conjecture`: `Odd (a n)` if and only if there exists a natural k with
`n + 1 = 2^k`. Since powers of two are positive, this is equivalent to
`n = 2^k - 1` for k >= 0, including n = 0 at k = 0.
The target has generality I because it imports the frozen
`D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity`, itself generality G.

## Falsifier

A natural index n whose coefficient has oddness different from membership
in {2^k - 1 : k >= 0} would contradict the assertion. The orchestrator's
exact coefficient check is supporting evidence only; it is not the universal
proof and imposes no finite bound on the theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.lean`.
- Main theorem and sole resolution anchor: `hanna_conjecture`.
- Companions: `term_coeff_eq_zero`, `generating_equation`, `generating_unique`,
  `mod_two_equation`, `mod_two_identity`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for all six public
  theorems, as reported in the implementation seat's envelope.
- Frozen dependency statement_id:
  `sha256:0033f4a50a501546a5f332ce1203c8cf1a936428e7a155a06a0443bb0f0f6232`.

The exact Lean statement of the coefficientwise equation is:

```lean
theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    ∀ N, coeff N generatingSeries =
      ∑ r ∈ Finset.range (N + 1), coeff N (term r generatingSeries)
```

## Triage

`theorem`. The formal proof closes the universal parity assertion recorded by OEIS.

## ASSUMED-UNVERIFIED

The quotes, attribution, and dates were supplied by the orchestrator; the
quotes were copied from the Library note. The OEIS entry and revision history
were read by the search seat on 2026-09-09, not by this seat. Literature scope
was the OEIS entry and revision history plus identifier searches on arXiv,
MathOverflow, and GitHub; this seat had no network access. Source-to-Lean
identification and first-publication priority are not kernel-checked facts.
The orchestrator's exact check and external build reports were not independently
rerun by this seat.
