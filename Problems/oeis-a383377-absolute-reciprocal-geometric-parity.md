---
slug: oeis-a383377-absolute-reciprocal-geometric-parity
bibkey: hanna2025a383377
doi: null
url: https://oeis.org/A383377
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity
---

# Parity of the A383377 coefficients

## Problem

Paul D. Hanna, OEIS A383377, May 15 2025. The following quotations are
verbatim from `Library/Arith/hanna2025a383377.md`.

NAME:

> G.f. satisfies A(x) = Sum_{n>=0} x^n * abs(1/A(x)^n), where abs(F(x)) equals the series expansion formed by the unsigned coefficients in F(x).

COMMENT:

> Conjecture: a(n) is even for n > 1.

## Motivation

This is a first-tier recent OEIS conjecture. KPI = open problems resolved.
The target module proves the assertion for every natural index greater than one.

## Gap

The search seat reported no proof found after reading the OEIS entry and revision
history on 2026-09-09 and performing identifier searches on arXiv, MathOverflow,
and GitHub. This Stage-B seat has no network and did not independently repeat
those searches. This bounded search does not establish publication priority.

## Route

`absSeries F` is `mk (fun n => |coeff n F|)`. The integer series A is built
by stabilised iteration (`approximation`) of the coefficientwise map Phi:
at each degree N its coefficient is the sum, for n from zero through N, of
`coeff N (X ^ n * absSeries (invOfUnit F 1 ^ n))`.
The map preserves constant coefficient one and improves agreement below degree
d to agreement below degree d+1, so each coefficient stabilises.

`generating_equation` states A(0) = 1 and, for every N,
`coeff N A = sum (n in range (N+1)) (coeff N (X^n * absSeries (invOfUnit A 1 ^ n)))`.
This is exactly the coefficientwise form of the OEIS infinite sum: summands
with n > N vanish at degree N. Mathlib has no infinite sums of formal series;
the honesty boundary is the finite coefficientwise statement, with no analytic
convergence or separate infinite-sum operator asserted.
`generating_unique` covers every integer series B with constant coefficient
one satisfying this equation.

Over `ZMod 2`, absolute values disappear. `geometric_fixed` establishes
coefficient agreement with arbitrary finite geometric sums, transports that
agreement through multiplication, and obtains F*(1 - X*U) = 1 with U*F = 1.
Consequently F = 1 + X (`mod_two_identity`). `hanna_conjecture` reads off
`Even (a n)` for n > 1. The module has no D5 import and declares generality G.

## Falsifier

A counterexample index n > 1 with odd a(n) in the uniquely defined integer
series would contradict the assertion. The orchestrator's exact coefficient
check is supporting evidence only, not the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_two_identity`.
- Axioms: std3, namely `propext`, `Classical.choice`, `Quot.sound`, for each
  public theorem, as recorded in the implementation seat's envelope.

## Triage

`theorem`. The formal proof closes the universal parity assertion recorded by OEIS.

## ASSUMED-UNVERIFIED

The OEIS quotations, attribution, and date were supplied by the orchestrator.
The OEIS entry and revision history were read by the search seat on 2026-09-09,
not by this seat. The reported literature scope was identifier searches on
arXiv, MathOverflow, and GitHub; this seat had no network access. No exhaustive
literature or first-publication claim follows. Source-to-Lean identification
and the reported source search are not kernel-checked facts.
