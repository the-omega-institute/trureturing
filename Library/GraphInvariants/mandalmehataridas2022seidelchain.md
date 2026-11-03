---
bibkey: mandalmehataridas2022seidelchain
authors: Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das
year: 2022
title: On the spectrum and energy of Seidel matrix for chain graphs
doi: 10.48550/arXiv.2205.00310
url: https://arxiv.org/abs/2205.00310v1
claim: "Conjecture 4.14 asserts the minimum Seidel energy of connected chain graphs and characterizes equality by Gamma(n,k)."
strata_touched:
  - D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum
license: citation-only
triage: anchor
---

# Minimum Seidel energy of chain graphs

## Verified locator

DOI: 10.48550/arXiv.2205.00310

Source: https://arxiv.org/abs/2205.00310v1

## Source definitions

Page 2, binary representation:

We represent a chain graph $G$ on $n$ vertices using a binary string $b=\alpha_1\alpha_2\alpha_3 \cdots \alpha_n$ of length $n$,
where $\alpha_i =0$ if the vertex $v_i$ is added as an isolated vertex, and $\alpha_i =1$ if the vertex $v_i$ is dominating to all the previously added isolated vertices. As we start from a single vertex we always take $\alpha _1=0$, and since we are considering connected graphs only so $\alpha_n=1$. For any $n$ vertex chain graph, without loss of generality, we represent it by the binary string $b=0^{s_1} 1^{t_1} 0^{s_2} \ldots 0^{s_k} 1^{t_k}$, where $s_i,~t_i \geq 1$ and $\sum\limits^k_{i=1}\,(s_i+t_i)=n$. A chain graph is a bipartite graph, and it is complete bipartite if and only if $k=1$.

Page 2, Seidel matrix, verbatim:

Let $G$ be a simple, connected, finite graph with vertex set $V=\{v_1,v_2,\ldots,v_n\}$. Let $A$ be the $(0,1)$-adjacency matrix [12, 17] of $G$. Then the Seidel matrix [1, 2, 6, 9, 19, 20, 22, 23, 25] is a square matrix of order $n$ defined by $S=J-I-2A$, where $J$ is all $1$ matrix and $I$ is the identity matrix.

Page 2, Seidel energy:

Obviously all eigenvalues of $S$ are real. We use $\lambda_1$ to denote the largest Seidel eigenvalue of graph $G$. The Seidel energy $SE(G)$ of a graph $G$ is defined as the sum of absolute values of the eigenvalues of Seidel matrix $S$.

Page 21, the comparison family:

Let $\Gamma_{n,k}$ be a class of chain graphs of order $n$ with the binary string $b=0^{s_1} \underbrace{1^{1} 0^{1} 1^{1} 0^{1}\ldots 0^{1}}_{2k-2} 1^{t_k}$ such that $s_1+t_k=n-2k+2$ with $1\leq s_1\leq n-2k+1$ and $1\leq t_k\leq n-2k+1$.

## Conjecture 4.14

Page 25, verbatim:

Let $G$ be a chain graph of order $n$ with the binary string $b=0^{s_1} 1^{t_1} 0^{s_2} \ldots 0^{s_k} 1^{t_k}$ such that $\sum\limits^k_{i=1}\,(s_i+t_i)=n,\,s_i\geq 1\,(1\leq i\leq k)$, and $t_i\geq 1\,(1\leq i\leq k)$. Then $SE(G)\geq SE(H)$, where $H\in \Gamma_{n,k}$. Moreover, the equality holds if and only if $G\in \Gamma_{n,k}$.

The encoding uses `Fin k` for the runs, `false` for 0 and `true` for 1. The graph vertices are the positions of the binary string. An edge joins an earlier 0 to a later 1. Natural subtraction in the endpoint bounds is truncated. The middle word consists of `k - 1` copies of `[true, false]`. The energy sums absolute real characteristic roots with multiplicity; the matrices used in the comparison are real symmetric.

## Mathematical scope

The comparison follows from the strict diagonal-simplex minimum for an odd signed core. Sign switching merges the first 0-run with the final 1-run. Compression separates the fixed additional eigenvalues from the core, and congruence preserves the inertia correction. The equality condition forces every intermediate run to be a singleton. The one-pair case has a common switched all-ones matrix minus the identity.

The numerical formula for the core inertia is not needed for this comparison. No assertion is made about minima for other blow-up cores or about the source's separate distinct-eigenvalue questions.

## Finite evidence

The finite checks are in [trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments/tree/f1f7a0711f88f1ffb836d47e29e7a83ec51625f0/docs/reports/mmd-seidel-chain), commit `f1f7a0711f88f1ffb836d47e29e7a83ec51625f0`. The file `docs/reports/mmd-seidel-chain/check.py` has SHA-256 `2c921a1141089050e3708af9184af68236d8665232e7ce1fd508542d4b2e47b3`. The preregistration records the command `/tmp/op-mmd2205/venv/bin/python -u /Users/auric/trureturing-experiments/docs/reports/mmd-seidel-chain/check.py`, exit 0, with final line `ALL_CHECKS_OK`: 66 source-fidelity cases, 11 cores, 511 compositions, 416 strict cases, 95 equality cases, and 466 gap/inertia certificates. These are finite computations, not a universal proof.

## Literature boundary

The source version is v1. The literature screen in [the preregistration](https://github.com/the-omega-institute/trureturing/issues/21681) found no settlement in the searched scope. Completeness is ASSUMED-UNVERIFIED: citation APIs were unavailable, exact-name queries do not cover every author variant, and no unindexed journal version is excluded.
