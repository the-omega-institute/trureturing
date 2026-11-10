---
bibkey: sunluoye2020projectionamgm
authors: R. Sun; Z.-Q. Luo; Y. Ye
year: 2020
title: "On the efficiency of random permutation for ADMM and coordinate descent"
doi: 10.1287/moor.2019.0990
url: https://arxiv.org/abs/1503.06387v3
claim: "Inspected arXiv v3 Section 3.3, Conjecture 3.1/(37), states the projection matrix AM-GM inequality; Section 4.3 Claim 4.1/(51a,b) gives its structured coordinate-descent identities."
strata_touched:
  - D5/S3/Quantum/Matrix/ProjectionAMGMRefutation
  - D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200
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

The historical formalized result supplies a three-dimensional rank-one projection counterexample to this unrestricted statement. The scalar200 companion supplies the complete scalar coordinate-descent refutation: an actual real unit independent basis at $n=N=200$, $P_i=I-a_i a_i^\top$, exponent $200$, all $200!$ reversed words and a strict quadratic form below $-1/16$. One such witness refutes the all-order assertion; it does not assert failure at every dimension. The optimal RP-CD rate and smallest failing dimension remain open.

The inspected locator is arXiv:1503.06387v3, Conjecture 3.1/(37), PDF p.20. Section 4.3, Claim 4.1/(51a,b), p.23, assumes square nonsingular concatenation with orthonormal columns within each block and states identities, which are not refuted. Its Remark after (54) explains the application. The scalar specialization takes every $d_i=1$. The weaker $G\preceq M$ in (52)–(53) survives. The journal PDF, journal numbering and journal/arXiv equivalence have not been independently verified; the legacy journal Conjecture 1 locator is not promoted to inspected evidence.

The named structured first-moment display is also recorded in [Kim–Lee–Yun](kimleeyun2025randompermutations.md). The ended source review had two approvals and one architecture comment about exact named-assertion status and existing-owner binding. Contextual namedness and the bounded inherited claim-specific search support this author's existing-owner interpretation; neither formula presence alone nor the parent conjecture's historical unproved wording establishes that its restriction remained open. Independent complete admission review remains required.

## Verified locator

DOI: https://doi.org/10.1287/moor.2019.0990

Source: https://arxiv.org/abs/1503.06387v3
