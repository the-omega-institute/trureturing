---
bibkey: pelekis2019orientationentropy
authors: Christos Pelekis
year: 2019
title: "On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs"
doi: 10.4418/2019.74.1.8
url: https://arxiv.org/abs/1808.04166
claim: "Conjecture 1.3 asserts degree balance for every orientation-count entropy maximiser; Section 4 asserts circular-hypergraph maximality."
strata_touched:
  - D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance
  - D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.4418/2019.74.1.8

Source: https://arxiv.org/abs/1808.04166

Published in Le Matematiche 74(1), 119–130. Page numbers below refer to the
journal PDF. Quotations preserve the words and mathematical symbols, with
line breaks and mathematical typesetting normalized.

## Definitions and source statements

Page 120: “The Shannon entropy (or entropy, for short) of a random variable X that takes values on a finite set S is defined as H(X) = −∑_{s∈S} P[X = s] · log P[X = s], with the convention 0 log 0 = 0. Throughout the text, log(·) denotes logarithm with base 2.”

Page 121: “Here and later, the class consisting of all r-uniform multi-hypergraphs on n vertices and m edges is denoted by D_{n,m,r}.” Repeated edges and isolated vertices are expressly allowed on the same page.

Page 121: “Here and later, the phrase random orientation on the edges of a hypergraph H expresses the fact that each edge in H is oriented towards one of its elements with probability 1/r, where each edge is oriented independently of all other edges.”

Page 122: “In other words, X_C is the number of vertices with non-zero in-degree after a random orientation on the edges of H_C and the above mentioned question on coloured dice can be equivalently expressed as follows.”

Page 122: “Given a hypergraph H = (V,ℰ) and a vertex v ∈ V, we denote by deg_H(v) the number of edges in ℰ that contain v.”

Conjecture 1.3, p. 122: “Let the positive integers m,n,r be such that m ≥ n > r ≥ 2. A hypergraph H = (V,ℰ) from D_{n,m,r} for which it holds H(X_H) ≥ H(X_G), for all G ∈ D_{n,m,r} is such that |deg_H(v₁) − deg_H(v₂)| ≤ 1, for all v₁,v₂ ∈ V.”

Section 4, pp. 128–129: “Fix a positive integer r ≥ 3. A circular r-uniform hypergraph on n > r vertices is defined as follows: Begin with a cycle C_n on n vertices, identified with ℤ_n. A proper subset I ⊂ ℤ_n is a path in C_n if it induces a connected sub-graph of the graph C_n. The size of a path is the number of vertices in the corresponding induced sub-graph. We call a hypergraph circular if (up to isomorphism) its set of vertices is equal to ℤ_n and its edges are paths of C_n of size r. We denote by C_{n,r} the circular hypergraph on n vertices whose edge set consists of all paths of size r.”

Section 4, p. 129: “We conjecture that circular hypergraphs are such that H(X_{C_{n,r}}) ≥ H(X_H), for all H ∈ D_{n,n,r}.”

## Encoding and scope

Vertices are `Fin n`; the ordered edge function `E : Fin m → Finset (Fin n)`
preserves multiplicities and isolated vertices. An orientation is a function
selecting one member of every edge. The literal filter of these functions equals
Mathlib's `Fintype.piFinset E`. For r-uniform edges, each orientation has
probability `1 / r^m`. The statistic `X E o` is the cardinality of the image of
`o`, and `deg E v` counts the indices of edges containing `v`.

The entropy sum ranges over `Finset.range (n+1)`, including zero-probability
outcomes, with an explicit parameter `r` for its denominator. In Conjecture
1.3 the ordered-pair inequality `(deg E v₁ : ℤ) − deg E v₂ ≤ 1`, quantified
over both orders, is equivalent to the source absolute-value inequality.
Circular edges start at each vertex `i` and contain `(i+j) mod n` for
`0 ≤ j < r`; for `n > r` these are exactly the n paths of size r.

## Refutations and remaining questions

The three-edge multigraph `{0,1},{0,1},{0,2}` has degrees `(3,2,1)` and
orientation counts `(0,1,5,2)`. It maximises entropy over all 27 ordered
2-uniform edge tuples on three vertices, contrary to Conjecture 1.3.

The four-edge multihypergraph `{0,1,2},{0,1,2},{0,1,3},{0,1,3}` has counts
`(0,2,27,44,8)` out of 81 orientations, while the circular hypergraph has
counts `(0,0,24,48,9)`. An exact integer product comparison implies strictly
larger entropy for the former. These finite refutations are repository-derived;
the source supplies the definitions and conjectures.

Conjecture 4.1, the asymptotic lower bound for circular hypergraphs, is a
separate statement and is not settled by either refutation. Degree-balance
optimality under additional restrictions and the three-vertex family for all
m ≥ 3 remain open here. The source's proved entropy bounds are separate
from its maximality conjectures.

## ASSUMED-UNVERIFIED

The supplied literature search found no settlement in its inspected scope;
it does not establish worldwide priority. The Pelekis–Schauer chapter,
“Network Coloring and Colored Coin Games”, Springer (2013), DOI
10.1007/978-1-4614-6825-7_4, was readable only as a subscription preview.
Its complete contents were not verified; the Firecrawl reading returned HTTP 402.
