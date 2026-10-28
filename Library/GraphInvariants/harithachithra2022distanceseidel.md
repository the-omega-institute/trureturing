---
bibkey: harithachithra2022distanceseidel
authors: T. Haritha and A. V. Chithra
year: 2022
title: Distance Seidel matrix of a connected graph
doi: 10.1080/09728600.2025.2479147
url: https://arxiv.org/abs/2210.05940v2
claim: "Problem 5.1 asks whether deleting any edge of K_{a,b}, with a,b > 1, strictly increases the distance Seidel energy."
strata_touched:
  - D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy
license: citation-only
triage: anchor
---

# Distance Seidel energy of complete bipartite graphs

## Verified locator

DOI: 10.1080/09728600.2025.2479147

Source: https://arxiv.org/abs/2210.05940v2

The arXiv version is v2. The journal version is titled “The distance Seidel matrix of connected graphs”. The quotations and page numbers below refer to arXiv v2.

## Source definitions

Page 2:

> D^S(G) = J − I − 2D = −1 if v_r is adjacent to v_t, 1 − 2d_G(v_r, v_t) otherwise.

> The distance Seidel energy E_{D^S}(G) of a graph G is defined as E_{D^S}(G) = Σ_{r=1}^n |∂_r^S|.

The equation J − I − 2D has diagonal zero, while the casewise expression has diagonal one. The Lean definition uses the matrix equation. Its energy sums absolute real characteristic roots with multiplicity; the distance matrices in the theorem are real symmetric.

## Problem 5.1

Page 13:

> Let G = K_{a,b}, with a, b > 1. Is E_{D^S}(K_{a,b} − e) > E_{D^S}(K_{a,b}), for any edge e of K_{a,b}?

The module proves the affirmative statement for every a,b ≥ 2 and every edge. Its supporting trace functional is unchanged by the rank-two edge perturbation; noncommutation makes the trace inequality strict. Propositions 5.2–5.3 give the cases with first part of size two and three. The universal Lean theorem uses the zero-diagonal matrix; the diagonal-one reading has only finite experiment evidence here.

## Literature boundary

The literature screen is partial; completeness is ASSUMED-UNVERIFIED. The preregistration is https://github.com/the-omega-institute/trureturing/issues/19532. The source and later works reached by that screen did not supply a general settlement.

## Finite comparison

The finite comparison for 2 ≤ a ≤ b ≤ 12 is in [trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments), commit `23a1280fffd81c90b7f5f6981dd13a24a390c3c3`, at `docs/reports/haritha-chithra-2022-distance-seidel-energy-problem-5-1/check.py` (SHA-256 `d98dd9d8b190718d24a193f64dc33e4f018260d706052b646d596a275a797405`). Running `/tmp/op-lwc-venv/bin/python /Users/auric/trureturing-experiments/docs/reports/haritha-chithra-2022-distance-seidel-energy-problem-5-1/check.py` exits 0 with `RESULT PASS`. This comparison checks both diagonal readings on that finite range; the universal Lean theorem concerns J − I − 2D.
