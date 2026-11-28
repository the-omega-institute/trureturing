---
bibkey: huhan2026signedsquareenergy
authors: Fu-Tao Hu and Xiao Han
year: 2026
title: "From the Square-Energy Conjecture to Signed Graphs: Sharp Bounds for Positive Square Energy"
doi: 10.48550/arXiv.2608.18492
url: https://arxiv.org/abs/2608.18492v1
claim: "Theorem 1.1 and Corollary 1.2 give the sharp signed square-energy bounds. Problem 6.1 asks for all equality cases at both endpoints."
strata_touched:
  - D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy
license: citation-only
triage: anchor
---

# From the Square-Energy Conjecture to Signed Graphs

For a finite connected signed simple graph with $n$ vertices and $m$ edges, let $s^+$
sum the squares of all strictly positive eigenvalues of the real signed adjacency,
counting multiplicities. Problem 6.1 asks for every graph attaining $s^+=2m-n+1$
and every graph attaining $s^+=n-1$, up to switching and isomorphism.
The paper gives signed trees at both endpoints, balanced complete graphs at the upper
endpoint, and antibalanced complete graphs at the lower endpoint. It also identifies the
intersection of the two extremal classes as the signed trees.
[Problem 6.1](https://arxiv.org/html/2608.18492v1#S6.Thmtheorem1)

Theorem 1.1 gives the upper bound, Corollary 1.2 gives the lower bound, and
equation (2.7) gives $s^++s^-=2m$. Theorem 3.1 gives the doubly nonnegative
matrix edge-sum inequality underlying the spectral bound.
[Source v1](https://arxiv.org/pdf/2608.18492v1)

The selected Lean declaration `HuHanSquareEnergy.result` proves both endpoint
equivalences for every connected `SimpleGraph (Fin n)` and signing of unordered
pairs. The signed adjacency reads the signing on edges and is zero on the
diagonal and on nonedges. The Hermitian eigenvalue family is indexed by all of
`Fin n`. A tree can have any signing. The two complete-graph cases require a
vertex sign assignment `θ` with edge entries `θ i * θ j` and `-(θ i * θ j)`,
respectively. The singleton belongs to both equality classes and has zero energy.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/33287)

## Verified locator

- DOI [10.48550/arXiv.2608.18492](https://doi.org/10.48550/arXiv.2608.18492)
- Source version [arXiv:2608.18492v1](https://arxiv.org/abs/2608.18492v1)
