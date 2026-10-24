---
slug: vom-ende-2024-gibbs-stochastic-simple-spectrum
bibkey: vomende2024diagonalizable
doi: 10.1142/S1230161224500124
url: https://arxiv.org/abs/2403.19643v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.result
---

# Simple-spectrum Gibbs-stochastic matrices for every positive Gibbs vector

## Problem

F. vom Ende, *Almost All Quantum Channels Are Diagonalizable*, arXiv:2403.19643v3 [quant-ph], Open Systems & Information Dynamics 31(3), 2450012 (2024), DOI 10.1142/S1230161224500124, leaves a construction question in the Outlook.

The v3 TeX source `channel_diag_approx.tex`, line 511, states:

> for the case of thermal operations, for example, one would have to first show that almost all Gibbs-stochastic matrices have only simple eigenvalues---regardless of the exact Gibbs state

Its footnote, lines 512–513, reads:

> For those interested: The last point is what makes this non-trivial. While the $\beta$-permutations \cite{Alhambra19,Mazurek19,PolytopeDegen22} are candidates for Gibbs-stochastic matrices with distinct eigenvalues many of them are only valid in certain parameter regimes, i.e.~only if the eigenvalues of the Gibbs state are interrelated in a specific way.
> We leave a general construction that is valid for all Gibbs states as an open problem.

These quotations are from the downloaded v3 source, md5 `18bc93c300903edbf34bf142ad00519d`; the source's definition of a simple eigenvalue as one of algebraic multiplicity one is at lines 123–125. See also [the literature note](../Library/QuantumContext/vomende2024diagonalizable.md).

Issue [#21152](https://github.com/the-omega-institute/trureturing/issues/21152) fixes the positive-Gibbs-vector reading: for every $n\in\mathbb N$ and every $d:\mathrm{Fin}\,n\to\mathbb R$ with $d_i>0$ for all $i$, there exists a real $n\times n$ matrix $P$ with nonnegative entries, every column summing to one, $Pd=d$, and no repeated roots in its complex characteristic polynomial. This existence statement is proved. Normalization of $d$ is not required; $n=0$ is included. The source's density consequence is separate from the formal claim.

## Motivation

In vom Ende (2024), arXiv:2403.19643v3, Lemma `lemma_hartfiel` (TeX lines 170–181) relates existence of one simple-spectrum element to density of such elements in an analytically path-connected class. The Outlook (lines 506–514) asks about applying this strategy to resource-theoretic channel classes and singles out Gibbs-stochastic matrices as a preliminary obstacle for thermal operations. A witness for every strictly positive Gibbs vector removes parameter restrictions from that classical construction problem.

## Gap

Issue #21152 records the bounded literature check before any Lean:

- the v3 source retains the question; the quoted source text and checksum are independently reproduced above;
- the reported check of five distinct citing works, related Gibbs-stochastic literature, arXiv searches combining Gibbs-stochastic matrices with simple spectrum, diagonalizability and birth–death chains, MathDB and google-deepmind/formal-conjectures found no settlement;
- the reported repository searches found no existing settlement of this question.

`not-found-in-searched-scope`. The classical simple-spectrum property of an irreducible real symmetric tridiagonal matrix is an ingredient, rather than the externally stated problem being settled.

## Route

All named helpers below are in `GibbsStochasticSimpleSpectrum` unless qualified otherwise.

1. **Normalize in positive dimension.** For $n=m+1$ and $d:\mathrm{Fin}\,(m+1)\to\mathbb R$ with $d_i>0$ for every $i$, put $g_i=d_i/\sum_jd_j$. Under exactly these hypotheses, `weights_positive` gives $g_i>0$ for every $i$, and `weights_sum` gives $\sum_i g_i=1$.
2. **Construct the path transition.** For any $n$ and real vector $g$, let $i\sim j$ mean $i+1=j$ or $j+1=i$ for the natural values of the finite indices, as in `Near`. Define $P=\operatorname{transition}(g)$ by $P_{jj}=1-\sum_{k\sim j}g_k/2$, $P_{ij}=g_i/2$ when $i\ne j$ and $i\sim j$, and $P_{ij}=0$ otherwise. For every $n,g$ and column $j$, `transition_columns` gives $\sum_iP_{ij}=1$. For every $n,g$ with $g_i\ge0$ for all $i$ and $\sum_i g_i\le1$, `transition_stochastic` gives column stochasticity. For every $n$ and real $g$, `transition_stationary` gives $Pg=g$. For $d$ of dimension $m+1$ with all entries strictly positive, `transition_preserves_weights` gives $\operatorname{transition}(\operatorname{weights}(d))d=d$. Thus the normalized construction belongs to `thermalProcesses d`, whose definition is column stochasticity together with preservation of $d$.
3. **Pass to a real Jacobi matrix.** For any $n,g$ with $g_i>0$ for every $i$, define $R=\operatorname{diag}(\sqrt{g_i})$ and $S=\operatorname{diag}((\sqrt{g_i})^{-1})PR$. Under these hypotheses, `symmetrization_charpoly` gives $\chi_P=\chi_S$. In dimension $m+1$, with every $g_i>0$, `symmetrization_jacobi` supplies real vectors $a,e:\mathrm{Fin}\,(m+1)\to\mathbb R$ such that $S=\operatorname{jacobiMatrix}(m,a,e)$ and $e_{t.\mathrm{castSucc}}\ne0$ for every $t:\mathrm{Fin}\,m$. Here `jacobiMatrix` is the diagonal matrix with entries $a$, plus the upper adjacent band with entries $e$, plus its transpose.
4. **Use endpoint uniqueness and the spectral theorem.** For every $m\in\mathbb N$ and real $a,e:\mathrm{Fin}\,(m+1)\to\mathbb R$ with $e_{t.\mathrm{castSucc}}\ne0$ for every $t:\mathrm{Fin}\,m$, `jacobi_eigenvector_zero` says: if a real vector $v$ and $\mu\in\mathbb R$ satisfy $Jv=\mu v$ for $J=\operatorname{jacobiMatrix}(m,a,e)$ and $v_{\mathrm{Fin.last}\,m}=0$, then $v=0$. Under the same conditions on $m,a,e$, `jacobi_simple` uses this fact and a Hermitian eigenvector basis to prove `HasSimpleEigenvalues J`. Equality of characteristic polynomials and `Matrix.charpoly_map` transfer the conclusion to $P$.
5. **Include the empty case.** For any $d:\mathrm{Fin}\,0\to\mathbb R$, `empty_case` uses the identity matrix, which is column stochastic, fixes $d$, and has characteristic polynomial $1$ with an empty root multiset. `result` splits the dimension into zero or $m+1$. In dimension one, the adjacent-edge hypothesis in the Jacobi argument is vacuous and the construction is $[1]$.

## Falsifier

The proof would not settle the preregistered statement if stochastic orientation, stationarity or algebraic multiplicity were changed. The definitions fix these points:

- `thermalProcesses d` means $P\in\operatorname{Matrix.colStochastic}(\mathbb R,\mathrm{Fin}\,n)$ and $Pd=d$; `Matrix.mem_colStochastic_iff_sum` identifies membership with nonnegative entries and column sums equal to one.
- `HasSimpleEigenvalues P` means that the multiset of roots of the characteristic polynomial of the entrywise complexification of $P$ has no repetitions. Over $\mathbb C$ this monic degree-$n$ polynomial splits, so this is the algebraic-multiplicity reading, rather than only a bound on eigenspace dimension.
- Strict positivity is required for every coordinate of $d$. Zero coordinates and microscopic realization as a thermal-operation channel are outside `claim`. The name `thermalProcesses` does not add a channel-realization assertion to its matrix definition.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.lean` (280 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.lean.json`, statement `sha256:4080473f7170fff2aeb77523f62e74f2f02af2f17c7a058d4844befbecacbb8b`.

Declaration statements:

- `result`: `sha256:ab05be053164951bb60ec7e203941e26ed45cc33d3b471547dc01741ca48f2b5`;
- `claim`: `sha256:932e11be5cd210c526d22870807824e1453f06724cf44d37f7ae9dba53e4e0a5`.

## Triage

Tier 1 open problem in the Outlook of a 2024 paper, preregistered in issue #21152 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural dimension $n$ and every real vector $d:\mathrm{Fin}\,n\to\mathbb R$ with every entry strictly positive, there exists a real $n\times n$ matrix $P$ with nonnegative entries, every column summing to one, $Pd=d$, and no repeated roots in its complex characteristic polynomial. The vector need not be normalized, and zero dimension is included.

**Argued, not formalized.**

- *Decisive mechanism and scope.* For a real Jacobi matrix of size $m+1$ whose $m$ adjacent coefficients are all nonzero, the endpoint-uniqueness property in `jacobi_eigenvector_zero` prevents two linearly independent eigenvectors from sharing an eigenvalue: a linear combination can cancel their last coordinates, hence must vanish. This is the mechanism used by `jacobi_simple` under precisely those edge hypotheses. The Gibbs-vector construction supplies them for every strictly positive $g$ in dimension $m+1$ by `symmetrization_jacobi`. No ordering, distinctness or inequalities among the Gibbs weights beyond positivity are needed. If some weights vanish, the inverse-square-root similarity is unavailable; no necessity of strict positivity for existence is asserted.
- *Gibbs interpretation.* For any fixed $T>0$ and strictly positive finite vector $d$, the real energies $E_i=-T\log d_i$ give $e^{-E_i/T}=d_i$. Conversely, finite real energies at $T>0$ give positive weights. Thus unnormalized positive vectors cover finite positive-temperature Gibbs weights, including repeated energy levels. This interpretation is not a formalization of thermodynamics or of zero-temperature limits.
- *Separation is not uniform for this construction.* In the three-dimensional family $g=(t,1-2t,t)$, $0<t<1/2$, put $a=1/2+t$, $b=t/2$ and $c=(1-2t)/2$. The matrix is $P=\begin{pmatrix}a&b&0\\c&1-t&c\\0&b&a\end{pmatrix}$. Direct determinant expansion gives $\det(xI-P)=(x-a)((x-a)(x-1+t)-2bc)=(x-a)(x-1)(x-1/2)$. For $0<t<1/2$ all weights are positive and all roots are distinct, but the distance between $1/2$ and $1/2+t$ tends to zero as $t\downarrow0$. Hence a uniform positive lower bound on separation of every pair of eigenvalues cannot be attached to this particular construction over all positive weights, even at fixed dimension three. Whether another construction provides a stronger uniform separation bound is not settled here.
- *Density consequence.* Fix $n\ge1$ and positive $d$, and let $\mathcal C_d$ be its Gibbs-stochastic matrices. The defining inequalities and linear equalities make $\mathcal C_d$ closed and convex. For any $A\in\mathcal C_d$, choose the witness $P_*\in\mathcal C_d$ from `result` and, for $t\in[0,1]$, put $A_t=(1-t)A+tP_*$. Its characteristic-polynomial discriminant is a polynomial in $t$, nonzero at $t=1$. It therefore has finitely many zeros, so simple-spectrum matrices $A_t\in\mathcal C_d$ approach $A$ as $t\downarrow0$ outside that finite set. For $n=0$ the assertion is trivial. This supplies the classical density consequence described by vom Ende (2024), arXiv:2403.19643v3, Lemma `lemma_hartfiel`; it is not part of the Lean type of `result`.
- *Effect on the source's remaining questions.* The classical witness requested in the Outlook footnote is supplied, and the preceding argument gives density for each fixed positive Gibbs vector. Extending the source's channel-density program to thermal operations would additionally require an element of that channel class with simple spectrum on its entire operator space; a Gibbs-stochastic population matrix alone does not supply that assertion. That bridge, the Outlook's LOCC extension, its eigenspace-preserving perturbation question (lines 517–518) and its dynamical approximation question (lines 521–527) remain unsettled by this result.

## ASSUMED-UNVERIFIED

The bounded literature check in #21152 establishes only `not-found-in-searched-scope`, not exhaustive worldwide novelty or priority. Its citing-work texts, arXiv version-history readings beyond v3, related Gibbs-stochastic definition source and search-catalog readings are not independently reproduced here. The v3 source quotation, checksum and DOI metadata are reproduced.

Everything under "Argued, not formalized" lies outside the formal assertion of `result`. In particular, the Gibbs-energy correspondence, separation analysis and density argument are not additional formalized conclusions. Existence for general vectors with zero coordinates, stronger uniform spectral separation from another construction, and the full-channel and dynamical extensions remain open here.
