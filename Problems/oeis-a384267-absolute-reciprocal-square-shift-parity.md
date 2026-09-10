---
slug: oeis-a384267-absolute-reciprocal-square-shift-parity
bibkey: hanna2025a384267
doi: null
url: https://oeis.org/A384267
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity
---

# Parity conjecture C.1 of OEIS A384267

## Problem

OEIS A384267, Paul D. Hanna, Jun 19 2025. The NAME and COMMENT below are
verbatim excerpts of the claim in `Library/Recurrence/hanna2025a384267.md`.

NAME:

> a(n) = abs([x^n] 1 + x/A(x)^2), where A(x) is the g.f.

COMMENT:

> (C.1) a(n) == binomial(3*n-1,n)/(3*n-1) (mod 2) (cf. A006013).

This dossier anchors exactly C.1 for n >= 1. The entry lists three conjectures;
C.2 (sign pattern) and C.3 (asymptotic ratios) are untouched. The companion
`a_zero` gives a(0) = 1. Here abs means coefficientwise absolute value of the
series `1 + x*A(x)^(-2)`, represented by the frozen `absSeries` applied to
`1 + X * invOfUnit (A ^ 2) 1`.

## Motivation

This is a first-tier OEIS conjecture from 2025. KPI = open problems resolved.
The target proves C.1 at every positive natural index, with no finite bound.

## Gap

The supplied search reports no proof found: the search seat read the OEIS entry
and revision history on 2026-09-09 and searched the identifier on
arXiv/MathOverflow/GitHub. This Stage-B seat has no network and did not repeat
that search. The reported scope is not an exhaustive literature survey.

## Route

`absSeries` is the frozen public definition of
`D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity`, reused by import,
not redeclared. A is the stabilized fixed point of
Phi(F) = absSeries (1 + X * invOfUnit (F^2) 1). The X factor raises the degree
of coefficient agreement, so the approximations stabilize. Thus
`generating_equation` states A(0) = 1 and
A = absSeries (1 + X * invOfUnit (A^2) 1), precisely the quoted NAME;
`generating_unique` covers every integer series B with constant coefficient 1
satisfying that equation.

Over ZMod 2, absolute value disappears and reciprocal cancellation gives
F^3 = F^2 + X for F = reduced A. The shift U = F + 1 satisfies U = X + U^3.
Factoring the difference of two cubic equations through a unit identifies
U = X*T(X^2). Here T is the reduced generating series of the frozen
`D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity`: its
`generating_equation` and `strip3_mod_two` give T = 1 + X*T^3 over ZMod 2,
and its `mod_two_identity` gives T = sum_n binomial(3*n,n)*X^n. Hence the
target's `mod_two_identity` gives reduced A = 1 + X*expand 2 T.

On the binomial side, `ternary_dvd` proves (3*n-1) divides binomial(3*n-1,n)
using gcd(n,3*n-1) = 1. `ternary_div_odd` gives
binomial(6*r+2,2*r+1)/(6*r+2) = binomial(6*r+1,2*r)/(2*r+1), while
`ternary_div_even` proves the positive even-index quotient even. Exact division
and Lucas reduction identify the quotient modulo 2 with binomial(3*r,r) at
n = 2*r+1 and with 0 at n = 2*r > 0. These match 1 + X*T(X^2), proving
`hanna_conjecture`; `a_zero` handles the constant coefficient separately.

Target generality is I, importing both frozen providers. The checkout headers
record AbsoluteReciprocalSquareParity as I and StripThreeTernaryCatalanParity
as G; the supplied brief's description of both as G disagrees with the first
header. No Lean metadata was changed.

## Falsifier

A positive index n with a(n) % 2 different from
(binomial(3*n-1,n)/(3*n-1)) % 2 would contradict C.1. The orchestrator's exact
check is supporting evidence only; the theorem covers all n >= 1.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_two_identity`,
  `a_zero`, `ternary_dvd`, `ternary_div_odd`, `ternary_div_even`.
- Implementation-seat axiom report: all eight public theorems use exactly
  std3, `[propext, Classical.choice, Quot.sound]`.
- Frozen statement IDs: AbsoluteReciprocalSquareParity,
  `sha256:1621c4931e1a6b728bb77e2c817029ba5b99f407028a1df9b0d9d3c650248fdf`;
  StripThreeTernaryCatalanParity,
  `sha256:f6a830f032e50c0283ce25e3b188ab6bc9e939530d207b3bbbf6a562d42799a7`.

Exact Lean statements (proof bodies omitted):

```lean
theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries = absSeries (1 + X * invOfUnit (generatingSeries ^ 2) 1)

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) :
    a n % 2 = ((Nat.choose (3 * n - 1) n / (3 * n - 1) : ℕ) : ℤ) % 2
```

## Triage

`theorem`. C.1 is resolved for every n >= 1; C.2 and C.3 are untouched.

## ASSUMED-UNVERIFIED

The quotes and attribution were supplied by the orchestrator and copied from
the Library note. The OEIS revision history was read by the search seat, not
this seat. The reported literature scope was the OEIS entry and revision
history on 2026-09-09 plus identifier searches on arXiv/MathOverflow/GitHub.
This seat had no network. Literature exhaustiveness, first-publication
priority, and source-to-Lean identification are not kernel-checked facts.
The numerical check and prior compilation/axiom reports are attributed to
their supplying seats; Stage-B did not independently rerun them.
