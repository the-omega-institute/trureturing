---
bibkey: assumpcaocoutinhogodsil2026totalconformal
authors: Henrique Assumpção, Gabriel Coutinho and Chris Godsil
year: 2026
title: Total Conformal Rigidity in Graphs
doi: 10.48550/arXiv.2605.08508
url: https://arxiv.org/abs/2605.08508v2
claim: Section 9 asks whether there are graphs that are 2-conformally rigid but not 1-conformally rigid; Definition 1.2 specifies both extremal eigenvalue sums over the simplex of nonnegative normalized edge weights.
strata_touched: []
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2605.08508

Source: https://arxiv.org/abs/2605.08508v2

## Source statements

Section 9, printed page 20 asks: “Are there graphs that are 2-conformally rigid but not 1-conformally rigid?”

The Introduction, printed page 1 states: “Let G = (V,E) be a simple, connected, undirected graph on n vertices with at least one edge, and let A := A(G) denote its adjacency matrix.”

It states: “For an edge ab ∈ E, we define z_ab := e_a − e_b, where e_a ∈ ℝ^V denotes the a-th canonical basis vector, and we also let L_ab := z_ab z_ab^T.” Equation (1) is $\mathcal{L}(w) := \sum_{ab\in E} w_{ab}L_{ab} = \sum_{ab\in E} w_{ab}z_{ab}z_{ab}^T$.

The Introduction, printed page 2 states: “The simplex of valid edge weights is thus defined as Δ_E := {w ∈ ℝ^E: w ≥ 0, 1^T w = |E|}.” It also states: “For the remainder of the text, we shall use 1 to denote the all-ones vector with the appropriate dimension, which will be clear from the context.”

The eigenvalue order is stated as: “We shall order the eigenvalues of ℒ(w) as 0 = λ₁(w) ≤ λ₂(w) ≤ … ≤ λₙ(w).” It states: “By the nontrivial eigenvalues of ℒ(w), we shall mean λ₂(w),…,λₙ(w).” Additional zero eigenvalues remain nontrivial in this indexing.

Definition 1.2, printed pages 2–3 states: “Let S_k(w) and s_k(w) denote the sum of the k largest and k smallest nontrivial eigenvalues of ℒ(w), respectively, for some k ∈ [n−1].” It continues: “We say that G is k-conformally rigid if, for any w,w′ ∈ Δ_E,” followed by $s_k(w) \leq s_k(\mathbf{1})$ and $S_k(\mathbf{1}) \leq S_k(w')$.

The finite Lean vertex set is `Fin n`. Each undirected edge is represented once by its ordered endpoints `a < b`. The endpoint indicator differences are expanded in the Laplacian entries. Increasing eigenvalues have zero-based indices, so the smallest nontrivial sum uses indices 1 through k and the largest sum uses indices i with n ≤ i+k. The graph with five vertices and all edges except {0,1} answers the question affirmatively; this answer is derived in the repository rather than asserted by the source.

## Scope

This note cites version 2. The bounded literature screen is recorded in issue #26026; completeness of that screen is ASSUMED-UNVERIFIED. No claim about the other Section 9 questions or an all-order family follows from this single witness.
