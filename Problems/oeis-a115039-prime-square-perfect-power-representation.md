---
slug: oeis-a115039-prime-square-perfect-power-representation
bibkey: hilliard2006a115039
doi: null
url: https://oeis.org/A115039
triage: theorem
motivation_gids:
  - D5/S3/Arith/PrimeSquarePerfectPowerRepresentation
---

# Prime square perfect-power representation

## Problem

OEIS A115039 and A115038 state the same conjecture:

> Conjecture: There will always be an x,y,n such that x^2 + p = y^n for all primes p.

The quantified reading is: for every prime natural number `p`, there are
natural numbers `x`, `y`, and `n` with `2 <= n` and
`x^2 + p = y^n`. The lower bound is the standard perfect-power condition;
without it, exponent one makes the equation immediate.

## Motivation

The assertion asks for one nontrivial perfect-power representation for every
prime, including the even prime.

## Gap

At the 2026-09-17 reading, both entries still label the assertion a
conjecture. Repository, pinned Mathlib, Loogle, GitHub Lean-code, and scoped
literature searches found no theorem with the complete conclusion.

The search was not an exhaustive global priority investigation.

## Route

For an odd prime, write `p = 2t + 1`. Then

`t^2 + p = t^2 + 2t + 1 = (t + 1)^2`.

For the prime two, `5^2 + 2 = 3^3`. These choices have positive bases and
exponents at least two.

## Falsifier

A prime for which no natural witnesses satisfy the quantified equation would
refute the assertion. Finite searches can detect a bad construction but cannot
establish the universal statement.

## Evidence

`D5/S3/Arith/PrimeSquarePerfectPowerRepresentation.result` proves the full
quantified statement by the parity split above.

## Triage

theorem; resolution proved.

## ASSUMED-UNVERIFIED

No exhaustive global priority claim is made beyond the searched surfaces.
