---
bibkey: barrettcameronevanshallkempton2022laplacianspread
authors: Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton
year: 2022
title: On the Laplacian spread of digraphs
doi: 10.1016/j.laa.2023.01.016
url: https://arxiv.org/abs/2206.15410v1
claim: "Conjecture 20 asks for a universal upper bound on digraph Laplacian spread that is linear in the order with slope one."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1016/j.laa.2023.01.016

Source: https://arxiv.org/abs/2206.15410v1

The source is arXiv v1. The target is numbered Conjecture 20 in the HTML
rendering and Conjecture 6.7 on page 16 of the PDF. The journal version is
*Linear Algebra and its Applications* 664 (2023), 126–146; its contents have
not been checked here.

## Source definitions

Section 2, page 2, states:

> Let $\Gamma = (V,E)$ denote an unweighted simple digraph of order $n$, where $V$ is the vertex set and $E\subseteq V\times V$ is the edge set.

> We denote the *out-degree* of vertex $i\in V$ by $d^{+}(i)$, which is equal to the number of edges of the form $(i,j)\in E$.

> After indexing the vertex set as $V=\left\{1,2,\ldots,n\right\}$, we define the *adjacency matrix* of $\Gamma$ by $A=[a_{ij}]_{i,j=1}^{n}$, where $a_{ij}=1$ if $(i,j)\in E$ and $a_{ij}=0$ otherwise.

> Moreover, we define the *Laplacian matrix* of $\Gamma$ by $L=D-A$, where $A$ is the adjacency matrix of $\Gamma$ and $D$ is a diagonal matrix whose $i$th diagonal entry is $d^{+}(i)$.

The same page states:

> The *algebraic connectivity* of $\Gamma$ is given by

$$
\alpha(\Gamma)=\min_{\substack{\mathbf{x}\perp\mathbf{e}\\\|\mathbf{x}\|=1}}\mathbf{x}^{T}L\mathbf{x}.
$$

> Another related and useful quantity is

$$
\beta(\Gamma)=\max_{\substack{\mathbf{x}\perp\mathbf{e}\\\|\mathbf{x}\|=1}}\mathbf{x}^{T}L\mathbf{x}.
$$

Section 3, page 5, states:

> We define the *Laplacian spread* of a digraph $\Gamma$ by

$$
\operatorname{sp}(\Gamma)=\beta(\Gamma)-\alpha(\Gamma),
$$

> that is, $\operatorname{sp}(\Gamma)$ is equal to the length of the real part of $W_r(L)$.

The Lean expressions use `Fin n`, the out-degree Laplacian, and real
`EuclideanSpace` unit vectors with coordinate sum zero. The displayed
extrema are represented by `sInf` and `sSup` of their quadratic-value set.
For order at least two this set is nonempty and compact, so these are the
attained minimum and maximum. The 0/1 matrix and row sum are written inside
`laplacian`; the proof applies the existing natural-number adjacency
matrix of `FiniteGraphEntropy` after casting its entries to the reals.

## Source conjecture

Section 6, page 14, states: “Note that all conjectures are made for
unweighted digraphs.”

Page 16 states verbatim:

> The bound on the Laplacian spread of digraphs given in (3.2) can be reduced to a linear function in n with a slope of 1.

The corresponding source TeX is:

```tex
The bound on the Laplacian spread of digraphs given in~\eqref{eq:unwght-spread-bound} can be reduced to a linear function in $n$ with a slope of $1$.
```

Equation (3.2), page 6, is

$$
\operatorname{sp}(\Gamma)\le\frac52(n-1).
$$

A slope-one universal bound means one real intercept independent of both
the order and the graph. The formal claim quantifies over every order
`n ≥ 2` and every loopless `Digraph (Fin n)`, allowing opposite arcs and
imposing no balance, regularity or polygonality assumption.

## Refutation and scope

The five-vertex digraph in Figure 3 has adjacency rows
`00100`, `10111`, `11011`, `00000`, `00000`. The zero-sum vectors
`(2,26,−26,−1,−1)` and `(0,0,0,1,−1)` have squared norms 1358 and 2,
and Laplacian quadratic values before normalization 6816 and 0.
Replacing each vertex by an independent cluster of size `m` multiplies
the two normalized values by `m`. The spread is at least `3408m/679`,
exceeding the order `5m` by at least `13m/679`. This defeats every fixed
real intercept. The argument needs neither a full eigenvalue calculation
nor the exact spread of the blowups.

The restricted balanced and polygonal questions and the best universal
asymptotic slope remain separate. No consequence here contradicts the
source's general bound `5(n−1)/2`.

## Experiment and literature boundary

Exact Figure 3 root isolation and the finite cluster checks are in
`the-omega-institute/trureturing-experiments`, commit
`2189938c4555f35b12767dce2ac078784f928114`, directory
`docs/reports/bcehk-laplspread/`. The program `check.py` has SHA-256
`c37f6d846b9c1342f26d3284250e053c90313946f9f50d636cb8483fff3d6366`.
The recorded command is
`/tmp/op-bcehk/venv/bin/python /Users/auric/trureturing-experiments/docs/reports/bcehk-laplspread/check.py`,
exit 0. Its rational enclosure for the top root is
`[818065/162463, 537362/106717]`, giving the source's spread rounded to 5.035.
These are computational results, separate from the Lean proof.

The literature screen in issue #21874 found no settlement in its inspected
scope. Completeness remains ASSUMED-UNVERIFIED: citing-work queries were
rate-limited, some full texts and later versions were unavailable, and the
journal version was not read. No exhaustive priority claim is made.
