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

Section 9, printed page 20 asks: “Are there graphs that are $2$-conformally rigid but not $1$-conformally rigid?”

The Introduction, printed page 1 states: “Let $G = (V,E)$ be a simple, connected, undirected graph on $n$ vertices with at least one edge, and let $A := A(G)$ denote its adjacency matrix.” It defines $z_{ab} := e_a-e_b$, $L_{ab} := z_{ab}z_{ab}^T$, and equation (1) gives $\mathcal{L}(w) := \sum_{ab\in E}w_{ab}L_{ab} = \sum_{ab\in E}w_{ab}z_{ab}z_{ab}^T$.

The Introduction defines $\Delta_E := \{w\in\mathbb{R}^E: w\geq 0,\;\mathbf{1}^T w=|E|\}$ and states: “By the *nontrivial* eigenvalues of $\mathcal{L}(w)$, we shall mean $\lambda_2(w),\ldots,\lambda_n(w)$.” Additional zero eigenvalues remain nontrivial in this indexing.

Definition 1.2, printed pages 2–3 states: “Let $S_k(w)$ and $s_k(w)$ denote the sum of the $k$ largest and $k$ smallest nontrivial eigenvalues of $\mathcal{L}(w)$, respectively, for some $k\in[n-1]$. We say that $G$ is *$k$-conformally rigid* if, for any $w,w'\in\Delta_E$,” followed by $s_k(w)\leq s_k(\mathbf{1})$ and $S_k(\mathbf{1})\leq S_k(w')$.

The finite Lean vertex set is `Fin n`. Each undirected edge is represented once by its ordered endpoints `a < b`. Increasing eigenvalues have zero-based indices, so the smallest nontrivial sum uses indices 1 through k and the largest sum uses indices i with n ≤ i+k. The graph with five vertices and all edges except {0,1} answers the question affirmatively; this answer is derived in the repository rather than asserted by the source.

## Scope

This note cites version 2. The bounded literature screen is recorded in issue #26026; completeness of that screen is ASSUMED-UNVERIFIED. No claim about the other Section 9 questions or an all-order family follows from this single witness.
