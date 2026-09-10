---
slug: oeis-a122399-stirling-power-factorial-prime-period
bibkey: bala2022a122399
doi: null
url: https://oeis.org/A122399
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod
---

# Prime periods of the A122399 Stirling power-factorial sum

## Problem

OEIS A122399, entry by Vladeta Jovovic, Aug 31 2006; NAME attribution
supplied by the orchestrator: Paul D. Hanna, May 31 2022. The following
NAME and COMMENT text is copied verbatim from the claim in
`Library/Recurrence/bala2022a122399.md`.

NAME:

> a(n) = Sum_{k=0..n} k^n * k! * Stirling2(n,k).

COMMENT (Peter Bala, May 31 2022):

> Conjecture: Let p be prime. The sequence obtained by reducing a(n) modulo p for n >= 1 is purely periodic with period p - 1.

The theorem proves that p - 1 is a period for every prime p and every n >= 1.
It does not assert that this period is minimal.

## Motivation

This is a first-tier OEIS conjecture dated 2022 in an entry created in 2006.
The KPI is open problems resolved; the target is the universal conjecture,
with no finite bound on the prime or positive index.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did
not independently repeat those searches. These searches do not establish
exhaustive literature coverage or first-publication priority.

## Route

`a n` is the NAME verbatim over natural numbers:
`sum_{k <= n} k^n * k! * Nat.stirlingSecond n k`.
`stirling2_inclusion_exclusion` proves the integer identity
`k! * S(n,k) = sum_{j <= k} (-1)^(k-j) * C(k,j) * j^n`
by induction on the factorial-weighted Stirling recurrence. Its base case
uses the binomial theorem; its recurrence uses `Nat.choose_mul_succ_eq`.

`a_eq_window` reduces a(n) modulo p to the fixed window k < p. If p > n,
Stirling numbers above the diagonal vanish; terms with k >= p vanish
modulo p because p divides k!. The window identity includes n = 0.
Inclusion-exclusion then gives the double sum
`sum_{k < p} sum_{j <= k} (-1)^(k-j) * C(k,j) * (k*j)^n` in `ZMod p`.
Fermat's little theorem makes each nonzero base (p-1)-periodic, and for
zero bases both powers vanish when n >= 1. Summing proves
`bala_conjecture`: `(a (n + (p - 1)) : ZMod p) = a n`.
Induction proves `bala_conjecture_periodic` for every nonnegative multiple
of the period. Minimality of the period is not asserted.

The module has generality G and only Mathlib imports:
`Mathlib.Combinatorics.Enumerative.Stirling` and
`Mathlib.FieldTheory.Finite.Basic`.

## Falsifier

A prime p and an index n >= 1 such that a(n+p-1) and a(n) differ modulo p
would contradict the assertion. The orchestrator's exact numerical check
is supporting evidence only, not a proof of the unbounded statement.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.lean`.
- Main theorem: `bala_conjecture`.
- Companions: `stirling2_inclusion_exclusion`, `a_eq_window`,
  `bala_conjecture_periodic`; definition: `a` using `Nat.stirlingSecond`.
- Reported axioms for each public theorem: std3
  (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator's exact checks support the source identification;
  the theorem quantifies over all primes and all positive indices.

## Triage

`theorem`. The formal proof resolves the stated periodicity assertion,
without a minimal-period claim.

## ASSUMED-UNVERIFIED

The quotations and attributions were supplied by the orchestrator; the
quote text was checked against the local Library note. The OEIS entry and
revision history were read by the search seat on 2026-09-09, not by this
seat. The reported identifier search covered arXiv, MathOverflow, and
GitHub; no proof was found within that scope. This seat had no network
access. Exhaustive literature coverage, priority, source attribution,
and source-to-Lean identification are not kernel-checked facts.
