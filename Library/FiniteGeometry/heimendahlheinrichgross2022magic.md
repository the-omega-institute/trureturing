---
bibkey: heimendahlheinrichgross2022magic
authors: Arne Heimendahl; Markus Heinrich; David Gross
year: 2022
title: "The axiomatic and the operational approaches to resource theories of magic do not coincide"
doi: 10.1063/5.0085774
url: "https://arxiv.org/abs/2011.11651v3"
claim: "The paper shows that completely stabiliser-preserving channels strictly contain the stabiliser operations, describes stabiliser operations in a diagonal subpolytope through partitions of the nonzero vectors of F_d^n into affine subspaces, and conjectures which partition maximizes the resulting overlap bound."
strata_touched:
  - D5/S3/Quantum/Magic/AffinePartitionFlagMaximum
license: citation-only
triage: anchor
---

# Heimendahl, Heinrich and Gross, The axiomatic and the operational approaches to resource theories of magic do not coincide

A. Heimendahl, M. Heinrich and D. Gross, Journal of Mathematical Physics 63(11) (2022) 112201, DOI 10.1063/5.0085774; arXiv:2011.11651v3. Quotations are from the arXiv v3 TeX source.

For prime $d$, the paper writes the stabiliser operations in the diagonal subpolytope through states $\sigma=\frac1{d^n-1}\sum_{K\in\mathcal K}|K|\,|s_K\rangle\langle s_K|$, where $\mathcal K$ is a disjoint partition of $\mathbb F_d^n\setminus0$ by affine spaces. It bounds $\langle+|\sigma|+\rangle\le\frac1{d^n(d^n-1)}\sum_{K\in\mathcal K}|K|^2$ and conjectures:

> We conjecture that such a projective measurement which maximizes \eqref{eq:estimation-of-overlapII} has the following form

namely measuring the qudits in turn in the computational basis until a nonzero outcome occurs. The induced partition consists of the sets of vectors with a given first nonzero coordinate and value; with coordinates indexed from $0$, the cell whose first nonzero coordinate is $i$ has $n-1-i$ free coordinates. The paper writes the cells as $xe_i+(0^i\oplus\mathbb F_d^{n-i})$ with $|K|=d^{n-i}$ for $i=0,\dots,n-1$, which counts one free coordinate too many; its sum $\sum_{k=0}^{n-1}(d-1)d^{2k}$ matches the cells of the measurement procedure. The paper evaluates the resulting sum $\sum_{k=0}^{n-1}(d-1)d^{2k}$ as $(d-1)\frac{d^{2n-2}}{d^2-1}$; the sum equals $\frac{d^{2n}-1}{d+1}$.

## Verified locator

Source: https://arxiv.org/abs/2011.11651v3
- DOI: https://doi.org/10.1063/5.0085774 (journal version; title, authors, journal, volume, issue and article number from Crossref; the journal text was not read).
- URL: https://arxiv.org/abs/2011.11651v3. The e-print member `paper_new.tex` has 1749 lines and md5 `f65b57a3e1b428a8e064b31e48d0b70f`. Locations:
  - the prime dimension, l. 131;
  - the partition lemma for the diagonal subpolytope, l. 986–994;
  - the remark with the overlap bound, the conjecture and the evaluation of the sum, l. 1209–1254.
