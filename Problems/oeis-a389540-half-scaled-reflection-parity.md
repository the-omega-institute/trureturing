---
slug: oeis-a389540-half-scaled-reflection-parity
bibkey: hanna2025a389540
doi: null
url: https://oeis.org/A389540
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HalfScaledReflectionParity
---

# G.f. A(x) satisfies A(x)^2 = A(2*x - 2*A(x)) / 2.

## Problem

> NAME "G.f. A(x) satisfies A(x)^2 = A(2*x - 2*A(x)) / 2."
>
> COMMENT "Conjecture: a(n) is odd iff n = 2^k for k >= 0."

## Motivation

This is a first-tier recent OEIS conjecture. KPI = open problems resolved.

## Gap

No proof was found: the OEIS entry and revision history were read by the search seat on 2026-09-08, with identifier searches on arXiv, MathOverflow, and GitHub. This seat has no network.

## Route

The compositional inverse R is defined first by the integer recursion `r` (`inverseSeries`), and A is its inverse (`generatingSeries`). `generating_equation` gives the normalized integral solution of the cleared equation `2A² = A(2X − 2A)`, and `generating_unique` proves uniqueness by inverse-coefficient induction. The inverse recursion gives `R ≡ X + X² (mod 2)`, so `R(A) = X` reduces to `A + A² = X` (`binary_equation` / `inverse_mod_two`). Frobenius with strong induction (`parity_recurrence`) identifies the odd coefficients exactly at powers of two (`hanna_conjecture`). There is no D5 import; the development has generality G.

## Falsifier

A counterexample index would falsify the conjecture; the orchestrator's exact check is supporting evidence only.

## Evidence

- Module: `D5/S1/Recurrence/Invariants/HalfScaledReflectionParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`.
- Axioms: `std3`.

## Triage

`theorem`

## ASSUMED-UNVERIFIED

The quoted OEIS lines were supplied by the orchestrator. The OEIS revision history was read by the search seat, not by this seat. The literature scope is the OEIS entry and revision history plus identifier searches on arXiv, MathOverflow, and GitHub; this seat has no network.
