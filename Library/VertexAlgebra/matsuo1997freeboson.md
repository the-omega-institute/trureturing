---
bibkey: matsuo1997freeboson
authors: Atsushi Matsuo; Kiyokazu Nagatomo
year: 1997
title: A Note on Free Bosonic Vertex Algebra and its Conformal Vectors
doi: null
url: https://arxiv.org/abs/hep-th/9704060v1
claim: Divided derivatives of the free bosonic current have explicit contractions in the polynomial Fock realization.
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/VertexAlgebra/matsuo1997freeboson -->

# Divided derivatives in the polynomial Fock representation

Sections 2.1–2.3 of arXiv hep-th/9704060v1 discuss free bosonic fields,
the polynomial Fock realization, vacuum and state fields. Printed page 19
gives the contraction of the divided derivatives of orders a and b as

$$
(-1)^a\frac{(a+b+1)!}{a!b!}(y-z)^{-a-b-2}.
$$

Printed page 20 realizes positive modes as n times differentiation with
respect to x_n, negative modes as multiplication by x_{-n}, and mode zero
as charge. For charge zero and x_{j+1}=X_j, these are the modes used in the
complex polynomial Fock modules. Printed pages 21–22 discuss the vacuum
and the state-field correspondence. The divided derivative is 1/a! times
the ordinary derivative; its creation series has coefficient
binomial(j+a,a) X_{j+a}. The contraction constant is
(-1)^a (b+1) binomial(a+b+1,a).

The complement index domains in printed Theorem 2.1 and the x_i indexing
in Section 2.3 appear inconsistent. These displays are not copied as
formal statements. The source supplies classical background and the
normalization, rather than an exact statement of the all-integer
polynomial output formula or Lean proof terms. The actual formula requires
supported evaluation of the nested normal products and identification
with an independently defined weighted power-series convolution.

This paper is distinct from hep-th/9706118v1, *On axioms for a vertex
algebra and the locality of quantum fields*. Chu–Lin, arXiv
1812.11378v1 Section 3.1, supplies Heisenberg normalization background;
Tong's *String Theory* Section 4.3.3 supplies pairing background with
contraction -alpha'/2. Neither is an exact source for the labelled
coefficient formula in the unit-normalized realization. These formal
algebraic calculations do not assert analytic convergence, module fusion,
a Monster realization or spacetime dynamics.

## Locator

- Matsuo–Nagatomo, arXiv `hep-th/9704060v1`, Sections 2.1–2.3,
  printed pages 19–22:
  https://arxiv.org/abs/hep-th/9704060v1
