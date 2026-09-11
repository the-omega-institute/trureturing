---
slug: oeis-a389476-quadratic-reversion-dyadic-support-parity
bibkey: hanna2025a389476
doi: null
url: https://oeis.org/A389476
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity
---

# Dyadic parity support of the A389476 quadratic reversion

## Problem

OEIS A389476 (Paul D. Hanna, Oct 05 2025) gives the following NAME and
COMMENT, quoted verbatim from `Library/Arith/hanna2025a389476.md`.

NAME:

> G.f. A(x) satisfies: A( x - A(x)^2/(1 - A(x))^2 ) = x.

COMMENT:

> Conjecture: a(n) is odd iff n is a term of A027383, where A027383(2*m) = 3*2^m - 2 and A027383(2*m+1) = 4*2^m - 2 for m >= 0.

## Motivation

This is a first-tier recent OEIS conjecture, selected in the lane's dispatch
brief. The KPI is open problems resolved: the target is the full parity
classification at every positive index, not a finite numerical sample.

## Gap

The supplied search-seat record reports no proof found after reading the OEIS
entry and revision history on 2026-09-09 and searching by identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not repeat
those searches. This is a scoped absence-of-proof report, not an exhaustive
literature or first-publication claim.

## Route

The module constructs A = `generatingSeries` over the integers by coefficient
stabilization. `generating_equation` proves A(0) = 0, a(1) = 1,
`A.subst innerSeries = X`, and the pinning identity
`(1 - A)^2 * (X - innerSeries) = A^2`. The constant coefficient of `1 - A`
is one, so its prescribed unit inverse exists: `innerSeries` is exactly
`X - (A * invOfUnit (1 - A) 1)^2`, namely x - A^2/(1 - A)^2 as in OEIS.
`generating_unique` proves that every zero-constant integer series f with
`f.subst (X - (f * invOfUnit (1 - f) 1)^2) = X` equals A. Thus the
normalization and the equation identify the constructed sequence uniquely.

Over `ZMod 2`, P = `lacunarySeries` is defined by the support indicator of
`exists m, n + 2 = 3 * 2^m or n + 2 = 4 * 2^m`. Equivalently it is the
formal lacunary sum over m >= 0 of x^(3*2^m - 2) + x^(4*2^m - 2), with
support OEIS A027383. `lacunary_quadratic` proves
`P = X + X^2 + X^2 * P^2` using support recursion and Frobenius.

Put `v = invOfUnit (1 - P) 1` and `r = X + (P * v)^2` in characteristic
two. Reversing the algebra of that quadratic identity gives
`(1 + X) * r = P * v` and `r + X = (1 + X^2) * r^2`, hence
`X = r + r^2 + r^2 * X^2`. Substituting r in the quadratic identity and
using degree-contraction uniqueness proves the reduced OEIS equation
`P.subst (X - (P * invOfUnit (1 - P) 1)^2) = X`
(`lacunary_reversion`). Mapping the integer equation to `ZMod 2` and using
reversion uniqueness identifies A mod 2 with P (`mod_two_identity`).

Finally `hanna_conjecture (n : Nat) (_hn : 1 <= n)` reads off
`Odd (a n) iff exists m, n + 2 = 3 * 2^m or n + 2 = 4 * 2^m`.
The support equalities use n + 2 rather than truncated natural subtraction;
the products are at least three and four, respectively, so they are
equivalent to the OEIS wording n = 3*2^m - 2 or n = 4*2^m - 2.
The module has only Mathlib imports, no D5 import, and generality G.

## Falsifier

A positive index n whose integer coefficient a(n) has parity different from
the stated dyadic-support indicator would refute the assertion. The
orchestrator's exact check is supporting evidence only; the theorem has no
finite search bound.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `lacunary_quadratic`,
  `lacunary_reversion`, and `mod_two_identity`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), reported for all
  six public theorems by the implementation seat's `print_axioms` record.
- The orchestrator reported successful Lean, Lean-report, and emission
  checks before Stage-B edits; this seat did not rerun those checks.

## Triage

`theorem`. The formal proof closes the universal positive-index parity
assertion recorded by OEIS, including existence, normalization, uniqueness,
and the functional-equation identification of its integer series.

## ASSUMED-UNVERIFIED

The OEIS quotations, attribution, and date were supplied by the orchestrator
and transcribed from the Library note. The OEIS revision history was read by
the search seat, not by this network-disabled Stage-B seat. The reported
literature scope was the OEIS entry and revision history on 2026-09-09 plus
identifier searches on arXiv, MathOverflow, and GitHub; it was not an
exhaustive search of private indexes or all publications. First-publication
priority and the source-to-Lean identification are not kernel-checked facts.
The finite exact check and the implementation seat's axiom report were not
independently rerun by this seat.
