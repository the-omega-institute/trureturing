---
bibkey: linwangcai2023laplacianratio
authors: Zhen Lin; Jiajia Wang; Min Cai
year: 2023
title: The Laplacian spectral ratio of connected graphs
doi: 10.48550/arXiv.2302.10491
url: https://arxiv.org/abs/2302.10491v1
claim: "Conjecture 5.4 proposes star and parity-dependent broom bounds for the Laplacian spectral ratio of trees with at least eight vertices."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2302.10491

Source: https://arxiv.org/abs/2302.10491v1

Page numbers below refer to arXiv version 1.

## Laplacian and spectral ratio

Page 2 states: “The Laplacian matrix of G with n vertices, denoted by L(G), is given by L(G) = D(G) − A(G), where A(G) is the adjacency matrix and D(G) is the diagonal matrix of its vertex degrees. And the largest and second smallest Laplacian eigenvalues of G are called the Laplacian spectral radius and algebraic connectivity of G, denoted by µ1(G) and µn−1(G). The Laplacian spectral ratio of a connected graph G with n vertices is defined as R_L(G) = µ1(G)/µn−1(G).”

`lapEig G i` uses Mathlib's nonincreasing `eigenvalues₀` of the real symmetric `G.lapMatrix ℝ`, with zero-based index `i`; hence it represents µᵢ₊₁(G). `spectralRatio G` divides index zero by index `n - 2` when `2 ≤ n`, and is zero otherwise. The extension below order two does not affect the conjecture.

## Broom tree

Page 13 states: “A broom tree B_n^t, shown in Figure 2, is a tree obtained from the path P_{n−t−1} and the star K_{1,t} by joining one pendant vertex of P_{n−t−1} and the center of K_{1,t} by an edge.”

Figure 2 labels the center v0, the star leaves v1 through vt, and the path vertices v_{t+1} through v_{n−1}. The Lean `broom n t` is `SimpleGraph.fromRel` applied to the relation
`(i.val = 0 ∧ 1 ≤ j.val ∧ j.val ≤ t + 1) ∨ (t + 1 ≤ i.val ∧ i.val + 1 = j.val)` on `Fin n`. The operation symmetrizes the relation and removes loops.

## Conjecture 5.4

Page 16 states: “Let T be a tree with n ≥ 8 vertices. Then R_L(K_{1,n−1}) ≤ R_L(T) ≤ R_L(B_n^{(n−3)/2}) if n is odd; R_L(B_n^{(n−4)/2}) if n is even. The left (right) equality holds if and only if T = K_{1,n−1} (T = B_n^{(n−3)/2} or T = B_n^{(n−4)/2}).”

`conjParam n` is `(n - 3) / 2` when `n % 2 = 1`, and `(n - 4) / 2` otherwise. These operations are natural-number subtraction, remainder and division. `claim` includes both bounds and both equality characterizations; graph equality in those characterizations is read as graph isomorphism. The refutation concerns the upper bound: at order 19, the parameter is eight, while `broom 19 7` has strictly larger ratio than `broom 19 8`.

## Scope

The source is arXiv version 1. Completeness of the literature screen and whether the journal version retains the same conjecture are ASSUMED-UNVERIFIED. The journal publication is Lin, Cai and Wang, “New bounds on the Laplacian spectral ratio of connected graphs”, Czechoslovak Mathematical Journal 74 (2024), 1207–1220, DOI 10.21136/CMJ.2024.0170-24.
