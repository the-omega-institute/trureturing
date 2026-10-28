---
bibkey: vomende2022strictpositivity
authors: Frederik vom Ende
year: 2022
title: "Strict positivity and D-majorization"
doi: 10.1080/03081087.2020.1860887
url: https://arxiv.org/abs/2004.05613v4
claim: "For a positive definite D, a matrix A is D-majorized by B when some quantum channel maps B to A and fixes D. The paper relates strict positivity of channels to this order. It shows that D is the unique minimal element of its trace hyperplane, and that the pure basis state for a minimal entry of d is maximal among positive semidefinite matrices of that trace. In the vector case the set M_D(A) of matrices D-majorized by A is a polytope; in the matrix case it has infinitely many extreme points, and the paper asks whether finitely many remain after identifying extreme points related by unitaries commuting with D."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude
license: citation-only
triage: anchor
---

# vom Ende, Strict positivity and D-majorization

F. vom Ende, arXiv:2004.05613v4 [quant-ph]; Linear and Multilinear Algebra 70(19) (2022), 4023–4048. Quotations are from the v4 TeX source, with the source's macros `\unitvector` and `\conj` expanded.

A channel is a linear, completely positive, trace-preserving map, and $Q(n)$ denotes the channels on $\mathbb C^{n\times n}$. Definition `defi_matrix_D_maj`:

> Let $D\in\mathbb C^{n\times n}$ positive definite and $A,B\in\mathbb C^{n\times n}$. Now $A$ is said to be \textit{$D$-majorized} by $B$, denoted by $A\prec_D B$, if there exists $T\in Q(n)$ such that $T(B)=A$ and $T(D)=D$.

Equation `eq:def_MD` defines $M_D(X)$ as the set of all matrices $D$-majorized by $X$.

Theorem `d_matrix_minmax` (ii), for $d\in\mathbb R_{++}^n$ and $\mathfrak h_d^+$ the positive semidefinite matrices of trace $e^Td$:

> $(e^Td)|e_k\rangle\langle e_k|$ is maximal in $\mathfrak h_d^+$ with respect to $\prec_D$ where $k$ is chosen such that $d_k$ is minimal in $d$. It is the unique maximal element in $\mathfrak h_d^+$ with respect to $\prec_D$ if and only if $d_k$ is the unique minimal element of $d$.

The question in the Conclusion and Outlook:

> In the matrix case, however, the number of extreme points is infinite […] a straightforward argument shows that if $X$ is extremal in $ M_D(A)$ then so is $U^* XU$ for all unitaries $U$ which satisfy $[U,D]=0$. A way of bridging this gap could be to define the unitary equivalence relation
> $$\sim\;:=\{(X,UXU^*)\,|\,X\in M_D(A), U\in\mathbb C^{n\times n}\text{ unitary with }[U,D]=0\}$$
> for arbitrary $d\in\mathbb R_{++}^n$ and $A\in\mathbb C^{n\times n}$, and then look at the equivalence class of an extreme point $X$ of $M_D(A)$ under $\sim$. Whether one ends up with finitely many extreme points after factoring out the unitary equivalents for now remains open.

## Verified locator

Source: https://arxiv.org/abs/2004.05613v4
- DOI: https://doi.org/10.1080/03081087.2020.1860887 (Linear and Multilinear Algebra 70(19), 4023–4048; published online 17 December 2020; title, author, journal, volume, issue and pages from Crossref).
- URL: https://arxiv.org/abs/2004.05613v4. The e-print is a gzipped tar archive; its member `strictly_positive_qc_v2.tex` has 1257 lines and md5 `b8b3abce192b148593dafd02809eaccf`. Locations:
  - Section `ch:prelim`, l. 99; $Q(n)$ and $Q_X(n)$, l. 140–146;
  - Section `sec:matrix_d_maj`, l. 398; Definition `defi_matrix_D_maj`, l. 466–469;
  - Theorem `d_matrix_minmax`, l. 874–885, proof to l. 921;
  - Eq. `eq:def_MD`, l. 926–931;
  - Section Conclusion and Outlook, l. 1055; the question, l. 1058–1064.
- The arXiv record lists four versions (v1, 12 April 2020; v4, 17 June 2020) and the journal reference "Lin. Multilin. Alg., 70:19 (2022) 4023-4048" (arXiv API metadata).
