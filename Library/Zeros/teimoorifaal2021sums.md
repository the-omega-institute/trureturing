---
bibkey: teimoorifaal2021sums
authors: Hossein Teimoori Faal
year: 2021
title: Sums of Polynomials and Clique Roots
doi: 10.48550/arXiv.2112.09744
url: https://arxiv.org/abs/2112.09744v1
claim: "Conjecture 4.1 (p. 5): Let G be a connected K₄-free graphs, then G has only clique roots."
strata_touched:
  - D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots
license: citation-only
triage: anchor
---

# Teimoori Faal, *Sums of Polynomials and Clique Roots*

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2112.09744

Source: https://arxiv.org/abs/2112.09744v1

## Source statements

Conjecture 4.1, page 5:

> Let G be a connected K₄-free graphs, then G has only clique roots.

Section 2, page 3:

> The real root of the clique polynomial of G is called the clique root of G.

Equation (2.1), page 3, defines the clique polynomial as the finite sum
C(G,x) = ∑_{k=0}^{ω(G)} cₖ(G)xᵏ. Its coefficients count vertex-subset cliques,
and c₀(G) = 1. The formal encoding uses the existing integer clique polynomial
and expresses “only clique roots” by requiring every complex zero to have
imaginary part zero. The sum through the vertex count has the same coefficients,
since no clique has more vertices than the graph.

## Scope

The formal refutation uses a connected K₄-free graph with seven vertices and
clique polynomial 1+7X+14X²+9X³. The negative cubic discriminant −31 prevents
splitting over ℝ and yields a nonreal complex zero.

The uniform counterfamily of arbitrarily large vertex connectivity described
in issue #22515 remains open in Lean. The experiment in
`the-omega-institute/trureturing-experiments`, commit
`9cabbd8bde46e73d7b1277bb548168561fc43c84`, is
`docs/reports/clique-roots-k4free/check.py`, SHA-256
`e6388e5e172bb0a6defc419d7092933261213afd49af8772fa745f72627af438`.
The preregistration records `python3 check.py`, exit 0, `ALL_CHECKS_OK`;
those finite and symbolic computations are distinct from the finite Lean theorem.

The literature screen in #22515 located no settlement in its searched sources.
Completeness of prior-art clearance and absence of a journal version beyond
arXiv:2112.09744v1 are ASSUMED-UNVERIFIED.
