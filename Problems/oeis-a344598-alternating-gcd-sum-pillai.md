---
slug: oeis-a344598-alternating-gcd-sum-pillai
bibkey: bala2024a344598
doi: null
url: https://oeis.org/A344598
triage: theorem
motivation_gids:
  - D5/S3/Factorization/AlternatingGcdSumPillai
---

# Bala's alternating gcd-sum formula for A344598

## Problem

OEIS A344598 NAME (Seiichi Manyama, May 24 2021):

> a(n) = Sum_{k=1..n} phi(k) * (floor(n/k)^2 - floor((n-1)/k)^2).

FORMULA (Peter Bala, Jan 01 2024):

> Conjecture: a(n) = Sum_{k = 1..2*n} (-1)^k * gcd(k, 4*n). Cf. A344372. - _Peter Bala_, Jan 01 2024

Both quotations are copied verbatim from the claim in
`Library/Arith/bala2024a344598.md`. The target is the equality for every positive n.

**范围与诚实边界**: This is a modest identity (tier 1). The two divisor-sum
formulas `a(n) = Sum_{d|n} phi(d)*(2*n/d - 1)` and
`a(n) = Sum_{d|n} (2*d*tau(d) - sigma(d))*mu(n/d)` were already proved elsewhere
by Daniel Weber, as credited in Mikhail Kurkov's Mar 31 2026 comment. They are
not the target. The target is the alternating-gcd formula, which the search
seat's 2026-09-08 reading recorded as still marked Conjecture. Natural division
and truncated subtraction define a; the alternating sum and theorem subtraction
are in the integers.

## Motivation

This is a first-tier recent OEIS conjecture. KPI = open problems resolved,
not module counts or a finite prefix checked. The module proves the assertion
for every positive natural-number index.

## Gap

The supplied search reports no proof found: the search seat read the OEIS
entry and revision history on 2026-09-08 and searched the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not repeat
those searches. No-proof-found is restricted to that reported search scope.

## Route

The totient bridge `a_eq_two_pillai_sub` proves `a(n) = 2*pillai(n) - n`:
floor-square increments select the divisors of n, gcd fibres give the
totient-weighted quotient sum, and Mathlib `Nat.sum_totient` supplies n.

Two gcd bookkeeping identities finish the proof. `pillai_four_mul` proves
`pillai(4n) + 4*pillai(n) = 4*pillai(2n)` by an even/odd range decomposition
and equality of shifted odd-index gcd blocks. `altGcdSum_eq` proves
`2*altGcdSum(n) + 2n = 4*pillai(2n) - pillai(4n)` by a reflected-index
construction with endpoint accounting. Combining these identities gives
`bala_conjecture`. Imports are Mathlib-only; generality is G.

## Falsifier

A positive natural-number index n for which the defining totient sum differs
from the alternating gcd sum would contradict the assertion. The orchestrator's
exact numerical check is supporting evidence only, not the universal proof.

## Evidence

- Lean module: `D5/S3/Factorization/AlternatingGcdSumPillai.lean`.
- Main public theorem: `bala_conjecture`.
- Companions: `a_eq_two_pillai_sub`, `pillai_four_mul`, `altGcdSum_eq`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for each public
  theorem, as recorded by the implementation seat's `#print axioms` receipt.
- The main theorem quantifies over all `n : ℕ` with `1 ≤ n`; no finite search
  bound is a hypothesis.

## Triage

`theorem`. The formal proof closes Bala's universal alternating-gcd assertion.

## ASSUMED-UNVERIFIED

The OEIS quotes and attributions were supplied by the orchestrator and copied
from the Library note. OEIS revision history was read by the search seat on
2026-09-08, not by this seat. Literature scope is the OEIS entry and history
plus identifier searches on arXiv, MathOverflow, and GitHub, as reported above;
it is not an exhaustive literature search or a claim of first-publication
priority. This seat did not independently verify the online sources, the
orchestrator's numerical check, or the implementation seat's axiom receipt.
Source-to-Lean fidelity and publication priority are not kernel-checked facts.
