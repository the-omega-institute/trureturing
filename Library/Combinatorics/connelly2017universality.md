---
bibkey: connelly2017universality
authors: Erin Connelly, Nathaniel Grammel, Michael Kraut, Luis Serazo, Christino Tamon
year: 2017
title: "Universality in perfect state transfer"
doi: 10.1016/j.laa.2017.06.015
url: https://arxiv.org/abs/1701.04145v2
claim: "For the continuous-time quantum walk U(t) = exp(-i t A) of a graph with Hermitian adjacency matrix A, universal perfect state transfer means that for all vertices u, v some time gives |U(t)_{v,u}| = 1; a graph has property T if every nonzero entry of A has modulus 1. The paper notes that K_2 and Circ(0,-i,i) are the only known complex unit gain graphs with universal perfect state transfer and conjectures that Circ(0,-i,i) is the only circulant with property T which has universal perfect state transfer."
strata_touched:
  - D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer
license: citation-only
triage: anchor
---

# Universality in perfect state transfer

E. Connelly, N. Grammel, M. Kraut, L. Serazo, C. Tamon, arXiv:1701.04145
(v1 2017-01-16, v2 2017-01-19, the latest); Linear Algebra Appl. 531 (2017)
516–532. Subjects: quant-ph, math.CO.

The paper studies graphs whose continuous-time quantum walk
`U(t) = exp(−i t A)` has perfect state transfer between every pair of vertices
(universal perfect state transfer). It characterizes such graphs through
switching equivalence (`MA = BM` for a monomial matrix `M`) and the circulants
`Circ(a_0, …, a_{n−1})`, `C_{jk} = a_{k−j}`, and quotes the eigenvalue
criterion of Cameron et al. for circulants. The concluding section considers
complex unit gain graphs and states:

> We say a graph has {\em property $\TT$} if all of the nonzero coefficients
> in its adjacency matrix are complex numbers with unit magnitude.
> \begin{conjecture} $\Circ(0,-\ii,\ii)$ is the only circulant with property
> $\TT$ which has universal perfect state transfer. \end{conjecture}

The introduction adds: "The only known examples of complex unit gain graphs
with the universal property are the circulants $K_{2}$ and $\Circ(0,-\ii,\ii)$.
We conjecture that this set is unique."

## Verified locator

- DOI: https://doi.org/10.1016/j.laa.2017.06.015 (the journal text was not
  read).
- URL: https://arxiv.org/abs/1701.04145v2 (source retrieved 2026-10-01):
  `main.tex`, the quantum walk and perfect state transfer (l. 150–156), the
  universal property (abstract, l. 128–130), the circulant convention
  (l. 230–231), monomial matrices and switching equivalence (l. 241–243), the
  introduction's two examples (l. 210–212), the Cameron et al. criterion
  (l. 566–577), and property `𝕋` with the conjecture (l. 1150–1155).
