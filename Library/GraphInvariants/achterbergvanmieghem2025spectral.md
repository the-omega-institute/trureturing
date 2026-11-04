---
bibkey: achterbergvanmieghem2025spectral
authors: Massimo A. Achterberg, Piet Van Mieghem
year: 2025
title: "The spectral degree exponent of a graph"
doi: 10.48550/arXiv.2502.01815
url: https://arxiv.org/abs/2502.01815v1
claim: "Definition 2.1 defines the spectral degree exponent by equality of the largest adjacency eigenvalue and the degree power mean; Section 7 asks whether it is submodular."
strata_touched:
  - D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation
license: citation-only
triage: anchor
---

# The spectral degree exponent of a graph

## Verified locator

DOI: 10.48550/arXiv.2502.01815

Source: https://arxiv.org/abs/2502.01815v1

Definition 2.1 and equation (2.1), p. 1; Theorem 2.2, p. 2; Section 7, p. 15.

## Source statements

“The spectral radius λ₁ is the largest eigenvalue of the weighted adjacency matrix A of the graph G.” (p. 1.)

“The spectral degree exponent (SDE) of a simple, undirected, non-regular (but possibly disconnected and weighted) graph G is defined as the solution for q of the equation λ₁ = ((1/N) Σ_{i=1}^N d_i^q)^{1/q}.” (Definition 2.1, equation (2.1), p. 1.)

“The spectral degree exponent (SDE) exists, is unique and is bounded in q ∈ [2, ∞].” (Theorem 2.2, p. 2.)

“Several other properties of the SDE have not yet been established, e.g. whether the SDE is submodular or if the SDE can be used successfully in applications to enhance or reduce assortativity.” (Section 7, p. 15.)

The Lean statement uses unweighted `SimpleGraph (Fin n)`, its degree function and its real adjacency spectrum. It asks about edge sets on a fixed vertex set, with the inequality required whenever all four graphs have finite exponents. The four counterexample graphs have vertex set `Fin 5`, common edges `{01, 02, 03, 14, 23}`, and optional edges `24` and `34`. Finite exponents above 3 at the intersection and union, and below 3 at the two single-edge additions, refute this inequality. Exponent uniqueness and global monotonicity of power means are not needed for this argument. The question does not invalidate the paper's definitions or earlier theorems.

The experiment is `the-omega-institute/trureturing-experiments`, commit `9f3dcb3b`, file `docs/reports/achterberg-van-mieghem-2025-spectral-degree-exponent-submodularity/check.py`, SHA-256 `80286464841329a5980d58b789ba8104621b2ee054cad885c5b0f756418897d2`; issue #19958 records exit 0. Its blowup, induced-vertex and supermodularity computations are outside the Lean settlement. Literature completeness is `ASSUMED-UNVERIFIED`.
