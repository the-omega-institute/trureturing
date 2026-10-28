---
bibkey: carograswald2021markovian
authors: Matthias C. Caro; Benedikt R. Graswald
year: 2021
title: "Necessary criteria for Markovian divisibility of linear maps"
doi: 10.1063/5.0031760
url: https://arxiv.org/abs/2009.06666v3
claim: "The paper derives necessary criteria for a linear map to be infinitesimal Markovian divisible, including a bound of the determinant of a quantum channel by a product of its smallest singular values. Optimizing the number of singular values in that bound reduces to a matrix inequality for a probability vector p: with a_ij = (p_i + p_j)/2 and g_ij = sqrt(p_i p_j), the paper conjectures that the largest h(d) with A + G <= d, where A and G sum the h(d) largest entries of a and g, is h(d) = 2d - 5."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex
license: citation-only
triage: anchor
---

# Caro and Graswald, Necessary criteria for Markovian divisibility of linear maps

M. C. Caro and B. R. Graswald, arXiv:2009.06666v3 [quant-ph]; Journal of Mathematical Physics 62(4) (2021), 042203. Quotations are from the v3 TeX source, with the source's macro `\IR` expanded.

Section `SctCriteriaQuantum` bounds the determinant of a quantum channel by a product of its smallest singular values (Corollary `CrlQuDetVSProductSmallestSV`). The remark after Example `ExmOptimalityLinearOrder2` (l. 707) reduces the optimal number of singular values in that bound to the following conjecture (Conjecture `CnjAMGMMatrices`, numbered 4.19 in arXiv v3 and IV.19 in the journal):

> Let $p\in\mathbb{R}^d_{\geq 0}$ with $\sum\limits_{i=1}^d p_i = 1$. Define the matrices $a,g\in\mathbb{R}^{d\times d}$ via
> $$a_{ij} = \frac{p_i + p_j}{2},\quad g_{ij}=\sqrt{p_i p_j}.$$
> Denote by $a_k^\downarrow$ and $g_k^\downarrow$ the $k^{th}$ largest entry of $a$ and $g$, respectively. Define
> $$A = \sum\limits_{k=1}^{h(d)} a_k^\downarrow,\quad G = \sum\limits_{k=1}^{h(d)} g_k^\downarrow.$$
> We conjecture that the maximal integer $h(d)$ such that $A+G\leq d$ holds for any probability vector $p$ is given by $h(d) = 2d-5$.

The paper adds:

> We have tested this conjecture numerically for a wide range of dimensions.

## Verified locator

Source: https://arxiv.org/abs/2009.06666v3
- DOI: https://doi.org/10.1063/5.0031760 (Journal of Mathematical Physics 62(4), 042203; published online 13 April 2021; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2009.06666v3. The e-print is a gzipped tar archive; its member `main.tex` has 1026 lines and md5 `90d30bc5ee1bec2594a8dedbee860324`. Locations:
  - Section `SctCriteriaQuantum`, l. 395;
  - Corollary `CrlQuDetVSProductSmallestSV`, l. 703;
  - the remark and the reduction, l. 719–727;
  - Conjecture `CnjAMGMMatrices`, l. 728–738;
  - the numerical-testing remark, l. 739–740.
- The arXiv record lists v1 (14 September 2020) and v3 (30 October 2022) as first and latest versions, with the journal reference "Journal of Mathematical Physics 62, 042203 (2021)" (arXiv API metadata).
