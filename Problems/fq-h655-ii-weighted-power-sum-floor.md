---
slug: fq-h655-ii-weighted-power-sum-floor
bibkey: simic2007h655
doi: null
url: https://www.fq.math.ca/Problems/Aug2009advanced.pdf
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/SimicWeightedPowerSumFloorIdentity
---

# Fibonacci Quarterly H-655(ii): weighted power-sum floor

## Problem

The 2009 follow-up prints:

> Let {c_i}_{i=1}^n be a finite sequence of distinct positive integers and q > 1 be a natural number. Prove that ⌊Σ c_i q^{c_i} / Σ q^{c_i}⌋ = c, where c = max{c_i : i = 1, …, n}. Is it true that ⌊(q−1) Σ c_i q^{c_i} / Σ q^{c_i}⌋ = c(q − 1) − 1?

> No solution was received for the inequality proposed in part 2. The proposer claims that it follows in an analogous way as the proof of part 1 but the argument needs a closer examination.

The formal claim here is the n ≥ 2 part-2 statement. For a finite set `s : Finset ℕ` of distinct positive indices, with `2 ≤ s.card`, `∀ i ∈ s, 1 ≤ i`, and `2 ≤ q`, the rational expression is rendered with `Int.floor` as:

    ⌊((q : ℚ) − 1) · (Σ i ∈ s, (i : ℚ) · (q : ℚ)^i) / (Σ i ∈ s, (q : ℚ)^i)⌋ = (max s) · ((q : ℤ) − 1) − 1.

The endpoint n = 1 is disclosed but NOT claimed: the printed statement fails there because the floor is exactly `c(q − 1)`. Part 1 is NOT claimed.

## Motivation

Problem H-655(ii) is an open problem in the Fibonacci Quarterly follow-up. The theorem resolves its non-singleton case while keeping the singleton endpoint and the separate first part explicit.

## Gap

The dated search surfaces recorded for #7626 are: the official Fibonacci Quarterly Problems index, which exposes 36 advanced PDFs through 2017 and places H-655 only in `Aug2009advanced.pdf`; the search seat's 2006–2024 corpus reading (repo-prior); arXiv with zero hits because the export API was rate-limited; Crossref top-20 with no match; MathOverflow with zero hits; GitHub exact-title/formula search with zero hits; and Loogle/pinned Mathlib with no dominating theorem. OpenAlex budget was 0 and LeanSearch was empty (ASSUMED-UNVERIFIED). FQ 2018–2020 filenames returned 404, so later-year coverage was not reconstructed. No priority claim is made.

## Route

Set δ := (q − 1) · Σ(c − c_i)q^{c_i}/Σq^{c_i}. The claim is 0 < δ ≤ 1. The strict lower bound comes from a second index below c. The upper bound follows from the tail identity Σ_{i<c}((q−1)(c−i)−1)q^i = q^c − (c+1) and domination by the subset of indices. The centered expression then lies strictly between consecutive integers, and `Int.floor_eq_iff` gives the result.

## Falsifier

For distinct positive indices and q ≥ 2, a counterexample with at least two indices would falsify `simic_h655_ii`. Singleton inputs are the disclosed endpoint control: their floor is `c(q − 1)`, so they are outside the theorem's hypotheses.

## Evidence

- Module: `D5/S3/ArithSums/SimicWeightedPowerSumFloorIdentity.lean`.
- Theorem: `simic_h655_ii`, with std3 axiom closure.
- Kernel readings from Step 0: import minimization, serial Lean, header check, and profiler all passed.
- Exact-rational orchestrator sampling: 21235 instances with n ≥ 2, 0 failures; n = 1 fails.
- Probe sampling: 9117 exhaustive and 10000 random instances, 0 failures; singleton controls fail by exactly one.

## Triage

`theorem`

## ASSUMED-UNVERIFIED

- OpenAlex search budget was 0.
- LeanSearch was empty.
- FQ 2018–2020 filename coverage was not reconstructed after 404 responses.
- The bounded search surfaces do not establish exhaustive literature coverage or priority.
