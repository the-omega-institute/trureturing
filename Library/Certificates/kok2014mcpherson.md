---
bibkey: kok2014mcpherson
authors: Johan Kok; Susanth C
year: 2014
title: Introduction to the McPherson number, Upsilon(G) of a simple connected graph
doi: 10.48550/arXiv.1410.8637
url: https://arxiv.org/abs/1410.8637v1
claim: The McPherson number of a graph is the least number of iterated vertex explosions after which the underlying graph is complete; for the finite Jaco graph J_n(1), n >= 3, it is i - 1 or i according as the prime Jaconian vertex v_i is or is not adjacent to v_n, and the outdegree d+(v_n) is conjectured to be nonrepetitive exactly when Upsilon(J_n(1)) is.
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson
license: citation-only
triage: anchor
---

# The McPherson number

Source: https://arxiv.org/abs/1410.8637v1 (posted 31 October 2014), by Johan Kok and Susanth C.

## Definition

The McPherson recursion is a series of vertex explosions. On the first iteration a vertex
$v$ of $G$ explodes, creating an arc to every vertex $u$ with $vu\notin E(G)$; on later
iterations a vertex $w$ explodes, creating an arc to every vertex $z$ that is neither
adjacent to $w$ in $G$ nor joined to $w$ by an arc already created. The McPherson number
$\Upsilon(G)$ is the minimum number of explosions after which the underlying graph is
$K_n$. The paper notes that $\Upsilon(K_n)=0$ and that the order of explosions matters for
the intermediate mixed graphs.

## Jaco graphs

Theorem 2.3 (page 4) states, for $n\ge3$ and the prime Jaconian vertex $v_i$ of $J_n(1)$,
that $\Upsilon(J_n(1))=i$ if the edge $v_iv_n$ is absent and $i-1$ otherwise, and page 5
conjectures that $d^+(v_n)$ is nonrepetitive exactly when $\Upsilon(J_n(1))$ is. Kok, Linear
Jaco Graphs: A Critical Review (2016), restates this as Theorem 2.48 and Conjecture 2.48.1, and
Corollary 7 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124, derives
$\Upsilon(J_n(1))=b_n-1$ with $b_n=\lfloor(n+1)/\varphi\rfloor$ and the conjectured equivalence.

The repository proves directly, without the prime-vertex case split, that after any list of
explosions the underlying graph is complete exactly when the non-exploding vertices form a
clique, and that $\Upsilon(J_n(1))=b_n-1$ for every $n$: the labels below $b_n$ suffice, and
every clique of $J_n(1)$ has at most $n+1-b_n$ vertices. The nonrepetition equivalence then
holds for every $n\ge2$.
