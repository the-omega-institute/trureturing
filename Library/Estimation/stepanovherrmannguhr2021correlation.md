---
bibkey: stepanovherrmannguhr2021correlation
authors: Yuriy Stepanov; Hendrik Herrmann; Thomas Guhr
year: 2021
title: "Generic features in the spectral decomposition of correlation matrices"
doi: 10.1063/5.0054438
url: "https://arxiv.org/abs/2104.08966v1"
claim: "The paper bounds the largest eigenvalue of a correlation matrix and the weights of its eigenvectors on the normalized diagonal vector in terms of the mean correlation and the standard deviation of the correlation coefficients, shows that the top eigenvector carries the largest weight for large dimension on one subdomain of characteristics, constructs counterexamples on another, and asks what happens on the remaining domain."
strata_touched:
  - D5/S3/Estimation/CorrelationTopEigenvectorWeight
license: citation-only
triage: anchor
---

# Stepanov, Herrmann and Guhr, Generic features in the spectral decomposition of correlation matrices

Y. Stepanov, H. Herrmann and T. Guhr, Journal of Mathematical Physics 62(8) (2021) 083505, DOI 10.1063/5.0054438; arXiv:2104.08966v1. Quotations are from the arXiv v1 TeX source.

An $n\times n$ correlation matrix $C$ has mean correlation $c=\frac{2}{n(n-1)}\sum_{i>j}C_{ij}$ and standard deviation $\sigma=\sqrt{\frac{2}{n(n-1)}\sum_{i>j}C_{ij}^2-c^2}$. With $\lambda_1$ a largest eigenvalue and $w_j=\langle v_j,\delta_n\rangle^2$ for an orthonormal eigenbasis, $C$ satisfies $w_1<w_{\max}$ if $w_1<\max_{j\ge2}w_j$ for every such basis. On $A=\{c,\sigma>0,\ c^2+\sigma^2<1\}$ the paper shows $w_1=w_{\max}$ for large $n$ on $A_1=\{c\ge\frac12\text{ or }\sigma<c\}$ and constructs matrices with $w_1<w_{\max}$ on $A_2=\{\sigma>\sqrt3c\text{ or }c<\sigma<1-c\}$, and asks:

> Given $(c,\sigma) \in A \setminus (A_1 \cup A_2)$ and $n\geq 2$ sufficiently large, is there an $n\times n$ correlation matrix $C$ with mean correlation $c$ and standard deviation $\sigma$ such that $w_1<w_{\max}$ holds?

## Verified locator

Source: https://arxiv.org/abs/2104.08966v1
- DOI: https://doi.org/10.1063/5.0054438 (journal version; title, authors, journal, volume, issue and article number from Crossref; the journal text was not read).
- URL: https://arxiv.org/abs/2104.08966v1. The e-print member `Correl_Matrix_Eigen_Geometry.tex` has 1186 lines and md5 `f79500596fc31cd1125b4477e1bd05cc`. Locations:
  - the mean correlation and the standard deviation, l. 176–183;
  - the domains $A$, $A_1$, $A_2$ and the theorem on $A_2$, l. 510–523;
  - the question, l. 525–527;
  - the definition of "$C$ satisfies $w_1<w_{\max}$", l. 877–879.
