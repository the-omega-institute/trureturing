---
bibkey: kostochkayancey2014ore
authors: "Alexandr Kostochka; Matthew Yancey"
year: 2014
title: "Ore's conjecture on color-critical graphs is almost true"
doi: 10.1016/j.jctb.2014.05.002
url: https://doi.org/10.1016/j.jctb.2014.05.002
claim: "The critical-graph edge bound implies three-colorability for finite K4-free graphs whose every induced subgraph has at most three halves as many edges as vertices."
strata_touched:
  - D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity
license: citation-only
triage: anchor
---

# Critical edge density and three-colorability

Published in *Journal of Combinatorial Theory, Series B* 109 (2014),
pages 73–101. The [journal-version PDF on the author's website](https://kostochk.web.illinois.edu/docs/2016/jctb14-y.pdf)
contains the definition of criticality on page 74 and Theorem 4 on page 76.

## Published theorem

A finite simple graph is $k$-critical if it is not $(k-1)$-colorable but
every proper subgraph is $(k-1)$-colorable. Theorem 4 states that, for
$k\ge4$, every such graph satisfies

$$
|E(G)|\ge
\left\lceil
\frac{(k+1)(k-2)|V(G)|-k(k-3)}{2(k-1)}
\right\rceil.
$$

In particular, every finite simple $4$-critical graph satisfies

$$
|E(G)|\ge\left\lceil\frac{5|V(G)|-2}{3}\right\rceil.
$$

## Application to hereditary sparse graphs

Let $G$ be a finite simple graph with no $K_4$ subgraph, and suppose

$$
2|E(G[S])|\le3|S|
\qquad\text{for every }S\subseteq V(G).
$$

Then $G$ is three-colorable. Otherwise, a subgraph minimal among those
that are not three-colorable is $4$-critical. Writing its vertex and edge
counts as $v,e$, the published bound and hereditary sparsity give

$$
5v-2\le3e\le\frac92v,
\qquad v\le4.
$$

A $4$-critical graph has at least four vertices, and a graph on four
vertices that is not three-colorable is $K_4$, a contradiction.

For an indexed loopless multigraph, apply this argument to its underlying
simple graph. The indexed hereditary edge bound implies the simple one,
and a proper coloring of the simple graph colors every indexed edge.
Parallel edge indices remain distinct in any arithmetic count that uses
them.

## Reuse boundary

This note reuses the published critical-graph theorem. The existing
`BipartiteSubgraphDensity` module supplies indexed four-color and density
machinery; it does not formally prove the Kostochka–Yancey bound or the
three-color consequence above. These are ordinary mathematical source
and application statements, not additional Lean-verified declarations.

Three-colorability alone supplies neither a source-compatible arithmetic
replacement nor its counting or modulus-sum payment. It does not settle
existence of an odd distinct covering system or unrestricted Erdős #7.
No source text or code from the paper is vendored.
