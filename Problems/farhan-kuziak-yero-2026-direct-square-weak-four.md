---
slug: farhan-kuziak-yero-2026-direct-square-weak-four
bibkey: farhan2026weakdirect
doi: 10.48550/arXiv.2605.22307
url: https://arxiv.org/html/2605.22307v1#S3.p17.1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.result
---

# Weak-four metric dimension of complete graph direct squares

## Problem

Mohammad Farhan, Dorota Kuziak and Ismael G. Yero, *The weak k-metric dimension
of the direct product of complete graphs*, arXiv:2605.22307v1,
Section 3, paragraph `S3.p17.1`:

> The result above clearly leads to a question concerning the exact value of
> wdim4(Kn × Kn) when n ≥ 4.

Section 6, first bullet, asks for the remaining exact formula at k = 4 and
whether the upper bound in Theorem 3.3 is the exact value.
This is one question over all integer orders at least four.

### Exact value and semantics

For every integer $n\ge4$,

$$
\operatorname{wdim}_4(K_n\times K_n)
=2n+\left\lceil\frac{2n}{11}\right\rceil+\mathbf 1_{n=5}.
$$

The vertex set is $[n]\times[n]$. Two vertices are adjacent exactly when
both coordinates differ. This is the direct product in the source.
For $n\ge3$ the actual shortest-walk distance is zero at equal vertices,
one when both coordinates differ, and two otherwise. In the last case,
a third row and a third column give a common neighbor. The graph is connected.

A finite landmark set $S$ is weak four-resolving if

$$
\sum_{w\in S}|d(x,w)-d(y,w)|\ge4
\quad\text{for every distinct }x,y.
$$

The introductory source definition omits the word “distinct.” Proposition 2.2
explicitly restricts to distinct pairs and supplies the coordinate identities
used by the paper. Self-pairs have separation zero and cannot be intended
when the paper discusses positive k. The formal predicate retains this
explicit distinct-pair intent.

The dimension is the least cardinality of such a set. The formal construction
proves that its feasible family is nonempty for every order in the question;
the universal lower bound and an equality-size set prove attainment. Natural
number division represents the ceiling as $(2n+10)/11$.

At order nine the answer is twenty. The source upper bound is twenty-one
there, so Theorem 3.3 is not always sharp. The answer covers every order;
this strict inequality alone is not the whole result.

## Motivation

The source gives exact formulas for the other weak parameters and leaves
the weak-four case open. A universal formula also decides whether its
Theorem 3.3 upper bound is always sharp.

## Gap

The source does not supply the universal sharp lower bound, the exceptional
order-five obstruction or equality-size witnesses at every order.

## Route

View the landmarks as edges of a bipartite incidence graph on n row labels
and n column labels. If $g_i,h_j$ are its degrees, a same-row pair has
separation $h_j+h_{j'}+[(i,j)\in S]+[(i,j')\in S]$. For a rectangle,

$$
\Delta_S((i,j),(i',j'))+[(i,j)\in S]+[(i',j')\in S]
+2[(i,j')\in S]+2[(i',j)\in S]
=g_i+g_{i'}+h_j+h_{j'}.
$$

These are Proposition 2.2's identities, rederived from actual graph distances.
The row and column cardinality sums reuse the metric-independent original
incidence facts of `HammingWeakTwoMetricDimensionCore`; no Hamming metric
is substituted.

A set with fewer than $3n-2$ landmarks has incidence minimum degree two.
A three-edge path whose four vertices all have degree two would give a
product pair separated by at most three. In the subgraph on degree-two
vertices, an adjacent pair therefore cannot both have two internal neighbors.
Let L be the low-vertex set and B its outgoing-edge count. A local charge,
with internal transfers canceling by symmetry, gives $2|L|\le3B$.
The high vertices have degree at least three, B is bounded by their total
degree, and the degree-sum formula gives $24n\le11|S|$. This yields the
ceiling term whenever the set could improve on the construction.

At n = 5, eleven landmarks would leave exactly one degree-three row and
one degree-three column. A low vertex with two low neighbors forces a
four-cycle with degree total nine, again giving separation three. Thus
each of the eight low vertices requires an edge to a high vertex, while
the total high degree is six. Twelve landmarks are necessary.

For attainment, an incidence set suffices if it has minimum degree two,
no four-cycle, and degree total at least nine on every three-edge simple
path. Explicit designs at orders four through sixteen satisfy these
properties and have exactly the displayed cardinalities. Disjoint incidence
union and coordinate relabeling preserve the criterion. Adjoining the
order-eleven design adds eleven row labels, eleven column labels and
twenty-four landmarks. Strong induction proves attainment at every larger
order. The ambient direct-product graph is connected throughout; only its
landmark incidence graph is assembled from disjoint blocks.

## Falsifier

A weak-four set below the displayed value, or an order at least four with
no equality-size weak-four set, would contradict the asserted formula.
Distances and separation must use the direct product and every distinct pair.

## Evidence

The owning declaration is
`D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.result`.
Its graph, separation predicate and infimum use actual finite graph vertices,
actual shortest distances and every distinct pair. Finite base verification
is used only inside the universal construction; arbitrary-order coverage and
the lower bounds are separate mathematical proofs.

The source version and question anchors are exact. Completed bounded searches
of source identifiers, weak metric dimension, weak/direct-product terms and
visible arXiv results did not identify this formula in their inspected windows.
The Cartesian Hamming weak-two result addresses a different graph and parameter.
Classical ingredients include finite incidence counting, the degree-sum formula
and graph distance. No exhaustive worldwide priority claim is made.

## Triage

Theorem: one exact-value question over all orders at least four. The claimed
resolution is the owning universal theorem, together with its attained-minimum
and graph-metric bridges.

## ASSUMED-UNVERIFIED

Uninspected cited bodies, complete forward-citation networks, non-arXiv
literature, and worldwide priority remain unverified.
