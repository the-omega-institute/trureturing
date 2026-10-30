---
bibkey: grosjeanhuillet2016carleman
authors: Nicolas Grosjean; Thierry Huillet
year: 2016
title: "Some combinatorial aspects of discrete non-linear population dynamics"
doi: 10.1016/j.chaos.2016.10.004
url: "https://arxiv.org/abs/1610.05919v1"
claim: "For an iterated power series map with the Carleman matrix P(k,k')=[x^{k'}]φ(x)^k, the critical case α₁=1 is treated by a normalized Jordan-chain matrix W with PW=W(I+S), and the paper conjectures that W⁻¹(k,k')=σ(k−1,k'), a sum over strictly increasing index paths of products of entries of P."
strata_touched:
  - D5/S3/StatisticalMechanics/CarlemanJordanChainInverse
license: citation-only
triage: anchor
---

# Grosjean and Huillet, Some combinatorial aspects of discrete non-linear population dynamics

N. Grosjean and T. Huillet, Chaos, Solitons & Fractals 93, 71–79 (2016); arXiv:1610.05919v1. Quotations are from the v1 TeX source.

For $\phi(x)=\sum_{k\ge1}\alpha_kx^k$ with $\alpha_1\ne0$, the paper uses the upper-triangular Carleman matrix $P(k,k')=[x^{k'}]\phi(x)^k$, $k'\ge k\ge1$, to linearize the iteration $x_{n+1}=\phi(x_n)$. In the critical case $\alpha_1=1$ the matrix $P$ has unit diagonal and is not diagonalizable; the paper constructs columns $\mathbf w_k$ with $P\mathbf w_1=\mathbf w_1$, $P\mathbf w_k=\mathbf w_{k-1}+\mathbf w_k$ for $k>1$, normalized by $\mathbf w_1=(1,0,\dots)$, $\mathbf w_k(k')=0$ for $k'>k$ and $\mathbf w_k(1)=0$ for $k>1$, through a recursion that divides by $P(k'-1,k')=(k'-1)\alpha_2$. With $W$ the matrix of these columns, $\sigma(0,k')=\delta_{1,k'}$, $\sigma(k,k')=0$ for $k'\le k$, and $\sigma(k,k')=\sum_{1=i_1<\dots<i_{k+1}=k'}\prod_{l=1}^kP(i_l,i_{l+1})$ for $k'>k\ge1$, the paper states:

> Then, we conjecture that $W^{-1}(k,k^{\prime })=\sigma (k-1,k^{\prime })$, $k^{\prime }\geq k\geq 1$.

## Verified locator

Source: https://arxiv.org/abs/1610.05919v1
- DOI: https://doi.org/10.1016/j.chaos.2016.10.004 (Chaos, Solitons & Fractals 93, 71–79; title, authors, journal, volume and pages from Crossref).
- URL: https://arxiv.org/abs/1610.05919v1. The e-print member `snlmatrixRR.tex` has 1387 lines and md5 `8c08ca10132a50d7c92ce541ba3d2240`. Locations:
  - the power series and the Carleman matrix, Eq. (2), l. 126–141;
  - the critical case and the Jordanization, l. 400–437;
  - $\sigma$ and the conjecture, l. 441–452.
