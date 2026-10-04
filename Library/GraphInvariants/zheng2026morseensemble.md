---
bibkey: zheng2026morseensemble
authors: Chong Zheng
year: 2026
title: "On the Morse Ensemble Polynomial of Simplicial Complexes"
doi: 10.48550/arXiv.2605.24689
url: https://arxiv.org/abs/2605.24689v3
claim: "Definitions 1.1 and 6.1 define the Morse ensemble and the independence Morse ensemble; section 7 Open problem (4) asks whether the chromatic polynomial is always recoverable from the latter."
strata_touched:
  - D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation
license: citation-only
triage: anchor
---

# On the Morse Ensemble Polynomial of Simplicial Complexes

Chong Zheng, arXiv:2605.24689v3, math.CO, version 3 (2026-06-28).

Section 2, pp. 3–4:

> The face poset P(K) of a finite simplicial complex K is the partially ordered set of all simplices of K, ordered by inclusion. Its covering relations are precisely the pairs σ ≺ τ with σ ⊂ τ and dim τ = dim σ + 1.

> An acyclic matching on P(K) is a collection M of covering pairs (σ, τ) such that each simplex of K appears in at most one pair and such that the Hasse diagram, after reversing the matched edges, contains no directed cycle [12].

> The simplices not appearing in any pair of M are called critical. We write c_i(M) for the number of critical i-simplices.

Definition 1.1, p. 2:

> The Morse ensemble polynomial of K is

$$
ME_K(z_0,\ldots,z_d)=\sum_{M\in\mathcal A(K)}\prod_{i=0}^{d}z_i^{c_i(M)},
$$

> where A(K) denotes the set of all acyclic matchings on P(K).

The face poset uses nonempty faces: dimensions run from zero through d.
Proposition 2.1, p. 4, interprets the coefficient of z_0 as matchings with exactly one critical cell, a vertex.

Definition 6.1, p. 24:

> For a graph G = (V, E), the independence complex Ind(G) = {I ⊆ V | I independent in G} is a simplicial complex of dimension α(G)−1, where α(G) is the independence number, the size of the largest independent set.

> The independence polynomial I(G;t) = Σ_{k≥0} i_k(G) t^k records the number i_k(G) of independent sets of size k.

> We define the independence ME polynomial

$$
\Phi(G):=ME_{\operatorname{Ind}(G)}(z_0,z_1,\ldots,z_{\alpha(G)-1}),
$$

> the Morse ensemble polynomial of the independence complex of G.

Section 7, Open problem (4), p. 29:

> Recovery from Φ(G). Theorem 6.4 shows that Φ(G) determines ME_G, and hence the Laplacian spectrum of G. Which further graph parameters are functions of Φ(G)? For instance, is the chromatic polynomial χ(G; t) always recoverable from Φ(G)? For which restricted graph classes, such as forests, bipartite graphs, or planar graphs, does Φ(G) separate non-isomorphic graphs?

The paper defines acyclicity as absence of directed cycles. The formal Acyclic
predicate instead asks for a natural-valued rank strictly increasing along every
arc. They agree on finite directed graphs: a cycle contradicts strict increase,
while a topological order of an acyclic finite digraph gives the rank by position.

The formal encoding records the complete finite Morse-vector coefficient function.
Proper-colouring counts use labelled colours, so a differing count at a natural argument implies differing chromatic polynomials.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2605.24689
- URL: https://arxiv.org/abs/2605.24689v3
- PDF: https://arxiv.org/pdf/2605.24689v3 — Definition 1.1, p. 2; section 2, pp. 3–4; Definition 6.1, p. 24; section 7, Open problem (4), p. 29.
