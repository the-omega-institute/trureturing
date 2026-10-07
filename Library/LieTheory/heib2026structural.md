---
bibkey: heib2026structural
authors: T. Heib; D. E. Bruschi
year: 2026
title: "On the structural properties of Lie algebras via associated labeled directed graphs"
doi: 10.48550/arXiv.2601.16161
url: https://arxiv.org/abs/2601.16161v1
claim: "Conjecture 83 states that a minimal-graph-admissible Lie algebra with trivial center either has no proper non-empty vertex subset with the ideal-graph-property in its minimal graph, or is a direct sum of centerless components each of whose minimal graphs has no such subset."
strata_touched:
  - D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation
license: citation-only
triage: anchor
---

# Heib–Bruschi, Lie algebras via labeled directed graphs

T. Heib and D. E. Bruschi, *On the structural properties of Lie algebras via associated
labeled directed graphs*, arXiv:2601.16161v1 (22 January 2026; math-ph, cross-listed
quant-ph). Numbers below are those of the v1 PDF.

## Verified locator

DOI: 10.48550/arXiv.2601.16161.
Primary version: https://arxiv.org/abs/2601.16161v1 (the only version).
The TeX source `pr09_arXiv_01.tex` of v1 and the v1 PDF supply §I (conventions),
Definition 16 and Eq. (7) in §II.A, Algorithm 1 and the minimal-graph definition in §II,
and Definition 75 and Conjecture 83 (p. 48) in §IV.D.

## Source statements

Conventions (§I): "We denote any field with the symbol \(\mathbb{F}\) … we write
\(x\propto y\) if and only if there exists a constant \(\kappa\in\mathbb{F}^*\) such that
\(x=\kappa y\)".

Definition 16 (§II.A, Graph-admissible Lie algebra): "Let \(\mathfrak g\) be an \(n\)-dimensional
Lie algebra. We say that \(\mathfrak g\) is minimal-graph-admissible if it admits a basis
\(\{x_j\}_{j=1}^n\) such that the Lie bracket satisfies:
\([x_j,x_k]=\alpha_{jk} x_{\delta(j,k)}\) for all \(j,k\in\mathcal{N}:=\{1,\ldots,n\}\),
(7) where \(\boldsymbol{\alpha}\in\mathbb{F}^{n\times n}\) is an antisymmetric matrix and
\(\delta:\mathcal{N}\times\mathcal{N}\to\mathcal{N}\) is symmetric function … To ensure
consistency and for later convenience, we define \(\delta(j,k):=0\) whenever
\(\alpha_{jk}=0\) …, and set \(x_0:=0\)".

Algorithm 1 (§II): "draw a vertex \(v_j\) for every basis element \(x_j\in\mathcal{B}\)
… If there exists an element \(x_\ell\in\mathcal{B}\) such that
\([x_j,x_k]\propto x_\ell\), one draws a directed edge from \(v_j\) to \(v_\ell\), labeled
by \(v_k\)." A graph associated with \(\mathfrak g\) "is a minimal graph if
\(|V|=\dim(\mathfrak g)\)".

Definition 75 (§IV.D): "A subset \(W\subseteq V\) is said to satisfy the ideal-graph-property if
and only if no edge \(e\in E\) points from a vertex \(w\in W\) to a vertex
\(v\in V\setminus W\)."

Conjecture 83 (§IV.D, p. 48): "Let \(\mathfrak g\) be a minimal-graph-admissible Lie
algebra associated with the minimal graph \(G(V,E)\). Suppose the center of
\(\mathfrak g\) is trivial, i.e., \(\mathcal{Z}(\mathfrak g)=\{0\}\). Then one of the
following conditions must hold: (i) The vertex set \(V\) contains no proper non-empty
subset \(W\subsetneq V\) that satisfies the ideal-graph-property or (ii) The Lie algebra
\(\mathfrak g\) admits a decomposition as a direct sum
\(\mathfrak g=\bigoplus_{j\in\mathcal{J}}\mathfrak g_j\), such that each component
satisfies \(\mathcal{Z}(\mathfrak g_j)=\{0\}\), and every minimal graph
\(G(V_j,E_j)\) associated with each \(\mathfrak g_j\) contains no proper non-empty subset
\(W_j\subsetneq V_j\) that satisfies the ideal-graph-property."

## Scope

The paper motivates Conjecture 83 with \(\mathfrak{su}(2)\oplus\mathfrak{su}(2)\), whose
two summands have the ideal-graph-property. It names the two-dimensional affine algebra
\(\mathfrak{aff}(\mathbb F)\) (§I) as a solvable non-nilpotent example. arXiv lists only v1.
