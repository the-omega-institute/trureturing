---
bibkey: ginat2018alternating
authors: Omer Ginat
year: 2018
title: The method of alternating projections
doi: null
url: https://arxiv.org/pdf/1809.05858v1
claim: Powers of a fixed finite ordered product of orthogonal projections converge strongly to the projection onto the common intersection in real or complex Hilbert space.
strata_touched: []
license: arXiv nonexclusive-distrib-1.0; citation-only
triage: anchor
---

# Finite cyclic orthogonal projections

Section 4.2, Theorem 4.2 on printed page 21 (PDF page 24) of
arXiv:1809.05858v1 states Halperin's theorem for a real or complex Hilbert
space and an integer J at least 2. For closed linear subspaces
M_1,...,M_J, write T=P_J ... P_1 and let P_M be the orthogonal projection
onto their common intersection. Then the norm of T^n x-P_M x tends to
zero for every vector x.

The statement assumes no dimension, separability, positive-angle,
closed-sum, nonzero or distinctness condition. It asserts pointwise norm
convergence, without a rate or an operator-norm conclusion. Empty and
singleton lists are outside the displayed J-at-least-2 scope and are
included separately by the formal theorem's universal finite-list domain.

This is a later expository Oxford Part C dissertation. Its bibliography
[15] attributes the theorem to I. Halperin, *The product of projection
operators*, Acta Sci. Math. (Szeged) 23 (1962), 96–99. The original paper
is not a directly consulted source, and no assertion about its exact
wording is inferred from that attribution.

The formal proof uses the pinned Mathlib projection and mean ergodic
results and the existing fixed-window convergence upgrade. No external
Lean source, article text or PDF is redistributed. This note contains
bibliographic metadata, source locators and a paraphrase only; the
citation-only label grants no redistribution license to the source PDF.
The arXiv abstract page links the nonexclusive-distrib/1.0 deposit license.
