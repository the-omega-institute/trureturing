---
bibkey: sunluoye2020projectionamgm
authors: R. Sun; Z.-Q. Luo; Y. Ye
year: 2020
title: "On the efficiency of random permutation for ADMM and coordinate descent"
doi: 10.1287/moor.2019.0990
url: https://arxiv.org/abs/1503.06387v3
claim: "Section 3.3, Conjecture 1 proposes a matrix AM-GM inequality in the positive-semidefinite order for finite families of real projection matrices."
strata_touched:
  - D5/S3/Quantum/Matrix/ProjectionAMGMRefutation
license: citation-only
triage: anchor
---

# On the efficiency of random permutation for ADMM and coordinate descent

Sun, Luo, and Ye study random permutation for ADMM and coordinate descent. In Section 3.3 they write:

> We observe that we only need to prove a matrix AM-GM inequality for projection matrices. We conjecture that the following matrix AM-GM inequality holds.
>
> **Conjecture** (matrix AM-GM inequality for projection matrices). Suppose $P_i \in \mathbb R^{N \times N}, i=1,\dots, n$ are projection matrices, then
> $$\frac{1}{n!}\sum_{\sigma = (\sigma_1,\dots,\sigma_n) \in \Gamma} P_{\sigma_n} P_{\sigma_{n-1}} \cdots P_{\sigma_1} \preceq \left( \frac{1}{n} \sum_i P_i \right)^n.$$
>
> Here $\Gamma$ is the set of all permutations of $\{1,\dots,n\}$ and $X \preceq Y$ means that $Y-X$ is positive semidefinite. The paper says that proving this inequality would solve the open question of the best convergence rate of RP-CD for quadratic problems.

The formalized result supplies a three-dimensional rank-one projection counterexample to this unrestricted statement. The structured coordinate-descent class, the optimal RP-CD rate, and the case of an even number $n$ of projections remain separate questions.

## Verified locator

DOI: https://doi.org/10.1287/moor.2019.0990

Source: https://arxiv.org/abs/1503.06387v3
