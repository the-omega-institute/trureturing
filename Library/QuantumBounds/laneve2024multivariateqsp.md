---
bibkey: laneve2024multivariateqsp
authors: L. Laneve, S. Wolf
year: 2024
title: "On multivariate polynomials achievable with quantum signal processing"
doi: 10.22331/q-2025-02-20-1641
url: https://arxiv.org/abs/2407.20823v2
claim: "Conjecture 8: if a three-level Protocol C segment A_m W̃ ⋯ A_1 W̃ maps a polynomial state of effective dimension ≤ 2 to one of effective dimension ≤ 2 while every intermediate state has effective dimension > 2, then the segment acts as a^k b^h · U on some pair of subspaces of dimension d ≥ 2; stated as the missing step towards Conjecture 7."
strata_touched:
  - D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation
license: citation-only
triage: anchor
---

# Laneve and Wolf, multivariate polynomials achievable with quantum signal processing

L. Laneve and S. Wolf, *On multivariate polynomials achievable with quantum signal processing*,
arXiv:2407.20823v2 (14 February 2025; quant-ph); Quantum 9, 1641 (2025),
DOI 10.22331/q-2025-02-20-1641.

## Verified locator

DOI: 10.22331/q-2025-02-20-1641.
Primary version: https://arxiv.org/abs/2407.20823v2 (the latest arXiv version).
The TeX source of v2 supplies Definition 1 (polynomial states), Protocol C and Definition 6
(effective dimension) in `contents/tripartite-protocol.tex` and the surrounding sections, and
Conjecture 8 (`thm:low-dim-identity-resolution`, lines 130–138 of that file).

## Source statements

Definition 1: "A polynomial state $|\gamma(z)\rangle$ is a polynomial vector in $z\in\mathbb T^m$ that
satisfies $\langle\gamma(z)|\gamma(z)\rangle\equiv1$."

Protocol C: "Consider the following signal operator $\tilde W=\operatorname{diag}(1,a,b)$. We
intertwine this operator with a sequence of processing operators $A_k\in SU(3)$ such that
$A_n\tilde W A_{n-1}\tilde W\cdots\tilde W A_0|0\rangle=|\gamma(a,b)\rangle$."

Definition 6: "A polynomial state $|\gamma(z)\rangle=\sum_k|\gamma_k\rangle z^k$ has effective dimension
$d$ if its coefficient vectors $|\gamma_k\rangle$ span a subspace of dimension $d$."

Conjecture 8: "Let $\ket{\gamma(\vv{z})}, \ket{\gamma'(\vv{z})}$ be polynomial states of effective
dimension $\le 2$ such that $\ket{\gamma(\vv{z})} = A_m \Tilde{W} A_{m-1} \cdots A_1 \Tilde{W}
\ket{\gamma'(\vv{z})}$ but any intermediate state has effective dimension $> 2$. Then the operator
$$A_m \Tilde{W} A_{m-1} \cdots A_1 \Tilde{W}$$ acts as $a^{k} b^{h} \cdot U$ in some pair of subspaces
$\calH \rightarrow \calH'$ of dimension $d \ge 2$, for some $U \in SU(d)$, $k, h \in \N$."

The text before it: "The final claim we could not prove in order to conclude Conjecture 7 is these
situations are the only possible cases that prevent an immediate translation."

## Scope

The paper proves sufficient conditions for multivariate QSP and gives Protocol C; Conjectures 7
and 8 are stated as open.
