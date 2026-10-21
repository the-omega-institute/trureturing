---
bibkey: guha2016multilayerpercolation
authors: Saikat Guha; Donald Towsley; Philippe Nain; Çağatay Çapar; Ananthram Swami; Prithwish Basu
year: 2016
title: "Spanning connectivity in a multilayer network and its relationship to site-bond percolation"
doi: 10.1103/PhysRevE.93.062310
url: https://arxiv.org/abs/1402.7057v4
claim: "For M independently site-percolated layers of a configuration-model graph with degree distribution p_k, the paper characterizes the multilayer site-percolation threshold q_c(M) as the smallest zero in [0, 1] of det A(q) for an explicit M × M matrix A(q), and conjectures that det A(q) has a unique zero in [0, 1] for all M ≥ 1 whenever C = Σ_k (k − 1) k p_k / z > 1."
strata_touched:
  - D5/S3/StatisticalMechanics/Percolation/MultilayerDeterminantRootNonuniqueness
license: citation-only
triage: anchor
---

# Spanning connectivity in a multilayer network and its relationship to site-bond percolation

S. Guha, D. Towsley, P. Nain, Ç. Çapar, A. Swami and P. Basu, arXiv:1402.7057v4 (2016-05-27); Phys. Rev. E 93, 062310 (2016). Quotations are from the v4 TeX source.

The binomial convention:

> where $\binom{j}{i}$ is defined to be zero whenever $i>j$.

The matrix:

> Consider the case $q_k=q$. We introduce the matrix $\bA(q) = [A_{ij}]$ with
> A_{ij} = \begin{cases} -C\Bigl(\binom{M}{j}-\binom{M-i}{j}\Bigr) q^j(1-q)^{M-j} & i\ne j \\ 1-C\Bigl(\binom{M}{j}-\binom{M-j}{j}\Bigr) q^j(1-q)^{M-j} & i=j \end{cases}
> where $C = \sum_k(k-1)kp_k/z$.

The conjecture:

> Numerically, it is easy to verify that $\det (\bA (q))$ has a unique zero in $[0,1]$ for all $M \ge 1$ as long as $C > 1$. We conjecture that this is always true.

## Verified locator

- URL: https://arxiv.org/abs/1402.7057v4 (v4, 2016-05-27; source `layers_PRE_resubmit.tex`, md5 `6d533e1548b93ff76e504e408ec78bf8`):
  - z, l. 148;
  - the binomial convention, l. 161;
  - the matrix, l. 171–180;
  - the conjecture, l. 199 and 755;
  - the threshold proposition, l. 730–750.
- DOI: https://doi.org/10.1103/PhysRevE.93.062310.
