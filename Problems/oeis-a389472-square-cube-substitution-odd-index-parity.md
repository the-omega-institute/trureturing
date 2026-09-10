---
slug: oeis-a389472-square-cube-substitution-odd-index-parity
bibkey: hanna2025a389472
doi: null
url: https://oeis.org/A389472
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity
---

# Odd-index parity of the A389472 coefficients

## Problem

OEIS A389472, Paul D. Hanna, Oct 15 2025, gives the following NAME and
COMMENT, quoted verbatim from `Library/Arith/hanna2025a389472.md`:

> G.f. satisfies A(x) = A(x^2 + x^3)/x^2 - 1.

> Conjecture: a(2*n-1) = 0 (mod 2) for n > 1.

范围与诚实边界: The separate comment "Conjecture: a(3*n-1) = 0 (mod 3)
for n > 1." is not resolved here. The generating equation alone leaves a(2)
free. The module fixes a(0)=0, a(1)=a(2)=1, matching the OEIS PARI program
and DATA, and formalizes the cross-multiplied identity
`x²(A+1) = A(x²+x³)` over integer formal power series. Only the first,
odd-index parity conjecture for that normalized sequence is claimed.

## Motivation

This is a first-tier recent OEIS conjecture, selected in the lane brief.
KPI = open problems resolved. The target is an assertion for every n > 1,
not a finite verification of initial coefficients.

## Gap

The supplied search-seat record reports no proof found: the OEIS entry and
revision history were read on 2026-09-08, with identifier searches on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not
independently repeat those searches. No exhaustive literature search or
first-publication priority is asserted.

## Route

The sequence is defined by a finite coefficient kernel with seeds a(0)=0,
a(1)=a(2)=1. `generating_equation` proves those seeds and
`x²(A+1) = A(x²+x³)`; `generating_unique` proves uniqueness among integer
series satisfying that equation with those seeds. For n >= 3,
`coeff_recurrence` gives
`a(n) = Σ_{k=0}^{floor(n/2)+1} a(k)·C(k, n+2−2k)`.

For an odd index m >= 3, the lower binomial index m+2−2k is odd. If k is
even, C(k, odd) is even; if k is odd and at least 3, it is a smaller odd
index, so strong induction makes a(k) even. The k=1 term vanishes because
C(1,m)=0. Thus every summand is even, proving `hanna_conjecture`.
The module has no D5 import, uses only
`Mathlib.RingTheory.PowerSeries.Substitution`, and declares generality G.

## Falsifier

An index n > 1 with odd a(2*n-1) in the normalized sequence would contradict
the assertion. The orchestrator's exact check is supporting evidence only;
no finite check substitutes for the universally quantified Lean proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `coeff_recurrence`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), reported for
  each public theorem by the implementation seat.

## Triage

`theorem`. The formal proof closes the first, modulo-two assertion for the
normalized sequence, with existence and uniqueness proved. The modulo-three
comment is outside this resolution claim.

## ASSUMED-UNVERIFIED

The OEIS quotes, attribution, date, and PARI/DATA identification were supplied
by the orchestrator. The OEIS revision history was read by the search seat,
not by this Stage-B seat. Literature scope was the OEIS entry and revision
history plus identifier searches on arXiv, MathOverflow, and GitHub on
2026-09-08; no exhaustive search of other indexes was claimed. This seat did
not use the network. First-publication priority and the source-to-Lean
identification are not kernel-checked facts.
