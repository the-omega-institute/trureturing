---
slug: oeis-a146557-collinear-triple-square-divisibility
bibkey: bala2025a146557
doi: null
url: https://oeis.org/A146557
triage: theorem
motivation_gids:
  - D5/S3/Factorization/CollinearTripleCountDivisibility
---

# Square divisibility of the A146557 collinear-triple count

## Problem

OEIS A146557 records a collinear-triple count in `Z_n x Z_n`. Peter Bala's
conjecture is quoted verbatim from the orchestrator's source reading:

> Conjecture: if 3 does not divide n then n^2 divides a(n). - Peter Bala, Jul 24 2025

Max Alekseyev's formula, quoted verbatim from the supplied source:

> a(n) = n * Sum_{i,j,k} ( n * gcd(i,j,k) - gcd(i,n) - gcd(j,n) - gcd(k,n) + 2 ) * k, where the sum is taken over all triples of positive integers i,j,k with i+j+k=n.

## Motivation

This is a first-tier 2025 OEIS conjecture, selected as a recent explicit
conjecture for which the orchestrator's search found no published proof.
The KPI is open problems resolved, not modules, seats, or lines of code.
The target theorem is unbounded in the natural-number index.

## Gap

The orchestrator reports that web, arXiv, and MathOverflow searches on
2026-09-08 found no published proof. Stage B has no network access and has
not independently repeated those searches. The OEIS revision history was
not read. This is a bounded search report, not a claim of publication priority.

## Route

Let `T(n)` be the sum of Alekseyev's symmetric summand over positive
three-part compositions of `n`. Cyclic reindexing `(i,j,k) ↦ (j,k,i)`
preserves both the composition set and the summand. Thus the three
coordinate-weighted sums agree; adding them replaces the weight by
`i+j+k=n`, giving `3·a(n) = n²·T(n)`. If `3 ∤ n`, coprimality of `3`
and `n²` implies `3 | T(n)`. Write `T(n)=3q` and cancel `3` in the moment
identity to obtain `a(n)=n²q`.

## Falsifier

A natural number `n` with `3 ∤ n` and `n² ∤ a(n)` would contradict the
assertion. The supplied sequence values `a(3)=6`, `a(4)=32`, `a(5)=200`,
`a(7)=1470`, and `a(8)=2688` are consistent with it; `n=3` is outside
the hypothesis. Finite values are supporting checks, not the proof.

## Evidence

- Lean module: `D5/S3/Factorization/CollinearTripleCountDivisibility.lean`.
- Public theorem: `sq_dvd_a`.
- Public proof chain: `sq_dvd_a → three_dvd_summand_sum → three_mul_a_eq`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported
  by the implementation seat's `#print axioms` output for all three theorems.
- The theorem is quantified over all natural numbers satisfying `3 ∤ n`;
  no finite search bound is used.

## Triage

`theorem`. The formal proof closes the universal divisibility assertion
for the sequence defined by Alekseyev's formula. Its interpretation as
the geometric collinear-triple count retains the boundary below.

## ASSUMED-UNVERIFIED

The Lean sequence is DEFINED by Alekseyev's formula; the identification
with the geometric collinear-triple count is not formalized. The ordered
matrix count equals `6·a(n)` in the orchestrator's numerical checks for
`n ≤ 9` only; Stage B has not independently rerun them. The source quotes
and the negative publication search are supplied by the orchestrator.
The OEIS revision history was not read. First-publication priority and
the source-to-Lean identification are not kernel-checked facts.
