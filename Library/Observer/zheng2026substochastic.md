---
bibkey: zheng2026substochastic
authors: Hugh Zheng
year: 2026
title: Substochastic escape and the Neumann series in aldous-broder-lean
doi: null
url: https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean
claim: A finite real substochastic matrix with a uniformly strict positive-power row-sum bound has powers tending entrywise to zero, nonsingular identity-minus-matrix, and an entrywise Neumann series equal to its resolvent.
strata_touched:
  - D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape
license: Apache-2.0
triage: anchor
---

## Verified locator

https://github.com/YuZh98/aldous-broder-lean/blob/bd20382923d987fc54a9773e04a4bc22b851872c/EAB/Paper/ConfinedChain.lean

The source namespace is `EAB.Paper.Chain`. The source file has SHA256 `d235b9788731933c6f9b315b164ed71859748ca44658eef3cf033acfefbb8fba`.

## Scope

The retained definitions and proofs give nonnegative matrix powers, row-sum identities and bounds, monotone row sums, geometric decay along fixed-size blocks, entrywise power decay, nonsingularity of the identity minus the matrix, and the Neumann series. The strict escape hypotheses are a positive natural power and a common real row-sum bound strictly below one. No irreducibility assumption is used.

The owning namespace and imports are adapted; statement types and proof bodies are retained. The upstream pins Lean 4.30.0 and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; the source port compiles with this repository's Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. The full Apache 2.0 licence and original NOTICE are retained in `docs/reports/licenses/aldous-broder-substochastic.md`.

Replace this source port by direct applications when the repository's adopted Mathlib revision supplies equivalent declarations with the same quantified hypotheses and conclusions.
