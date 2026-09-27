---
bibkey: chulin2018heisenberg
authors: Yanjun Chu and Zongzhu Lin
year: 2018
title: Moduli spaces of conformal structures on Heisenberg vertex algebras
doi: null
url: https://arxiv.org/abs/1812.11378v1
claim: Section 3.1 gives the complex Heisenberg bracket, charge-zero vacuum representation, and normalized field expansion.
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/chulin2018heisenberg -->

# Heisenberg vertex algebra

Chu and Lin, Section 3.1, define the affine Heisenberg bracket, the
charge-zero vacuum representation, and the field expansion
$Y(h,z)=\sum_{n\in\mathbb Z}h(n)z^{-n-1}$ over $\mathbb C$. These are the
literature anchors for the normalized mode convention and Fock construction.

The rank-one polynomial formulas over $\mathbb Q$,
$a_{k+1}=(k+1)\partial/\partial X_k$,
$a_{-(k+1)}=X_k\cdot(-)$, and $a_0=0$ are an algebraic specialization of the
complex vacuum representation. The all-integer commutator relation and
second-order formal locality are standard consequences of these formulas;
changing the coefficient field or rewriting locality as a coefficient shift
does not make them new mathematical results. A future Lean construction of
the pointwise Laurent field would be a formalization contribution, not a
claim that Chu and Lin supply its Mathlib proof.

## Verified locator

- arXiv:1812.11378v1, Section 3.1:
  https://arxiv.org/abs/1812.11378v1
- The arXiv metadata and Section 3.1 source HTML were inspected on
  28 September 2026. The source uses $\mathbb C$; the rational polynomial
  realization above is a specialization.
