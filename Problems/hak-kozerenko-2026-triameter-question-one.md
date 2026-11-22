---
slug: hak-kozerenko-2026-triameter-question-one
bibkey: hakkozerenko2026triameter
doi: 10.48550/arXiv.2611.17259
url: https://arxiv.org/html/2611.17259v1#S7.p2.1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Triameter/CliqueChains.question1
  - D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.k1_equality_projection
  - D5/S3/Combinatorics/Graph/Triameter/DistanceProjection.triameter_ge_of_evenLegTriangle
---

# Hak–Kozerenko Question 1 at k = 1

## Problem

Artem Hak and Sergiy Kozerenko, *Triameter, distance packings, and vertex
connectivity*, arXiv:2611.17259v1, §7, printed p. 19.

> Question 1. Theorem 1.1 determines the distances between the vertices of a triametral triple in graphs attaining the equality in (1), but not the whole graph. Characterize the graphs attaining this equality, at least for k = 1, that is, the graphs G with tr(G) = 4α(G) − 1.

The source assumes a finite simple connected undirected graph of order at least
three. The triameter is the maximum of the sum of the three pairwise
shortest-path edge counts, with repetitions allowed. The independence number
is the maximum size of an independent set.

## Motivation

Equality in the triameter bound fixes the distances between the members of
a triametral triple. The classification determines every graph edge consistent
with attaining the bound at k = 1.

## Gap

The paper's equality conditions on the three distances leave the preimages
of the model blocks and the edges between them to be determined. The target is
the full equivalence at k = 1. The bounded literature search found the source's
even-leg triangle examples and two restricted classifications.
[Registered target](https://github.com/the-omega-institute/trureturing/issues/32242#issuecomment-7039574405) ·
[Literature findings and tier](https://github.com/the-omega-institute/trureturing/issues/32242#issuecomment-7040984355)

## Route

Project a maximizing triple to the feet of a three-legged graph whose centre
is a point or a triangle according to the parity of the perimeter.
The packing estimate and its equality conditions at k = 1 force a triangle
and leg lengths 2q(i). The projection is surjective and lifts the model edges.

The three roots form one block. Each successive pair of positive depths
2t−1 and 2t on a leg forms a peripheral block. For any block one can choose
q(0)+q(1)+q(2) mutually independent model vertices distinct from and
nonadjacent to all vertices of the block. Lifting them and adding a pair
of nonadjacent vertices of the inverse block would violate the independence
number. Thus each block preimage is a clique.

Every layer is a nonempty fiber. The three root layers partition the central
clique. Each peripheral clique is partitioned into its inward and outward
layers. The only edges between different cliques are at the interfaces from
depth 2t to 2t+1 on a single leg. These interfaces carry arbitrary nonempty
edge sets. At depth zero the interface starts in the corresponding layer of
the central clique. A leg of length zero has no interface.

Conversely, an independent set has at most one vertex in each clique. A
walk projects to a sequence of equal or adjacent model vertices. The three
lifted feet therefore give a perimeter of at least 4(q(0)+q(1)+q(2))+3.
The triameter upper bound by independence forces equality.

## Falsifier

An equality graph failing any of the layer, internal adjacency, allowed-edge
or nonempty-interface requirements would contradict necessity. A constructed
graph with a different triameter or independence equality would contradict
sufficiency, including when one or more chains are empty. The theorem
establishes both directions on the actual graph vertex type.

## Evidence

`D5/S3/Combinatorics/Graph/Triameter/CliqueChains.question1` proves the
equivalence with axiom closure `propext`, `Classical.choice` and `Quot.sound`.
`DistanceProjection.k1_equality_projection` specializes §3, Lemma 3.2
(p. 6), with the equality distances from the §4 proof of Theorem 1.1 (p. 10)
at k = 1. `DistanceProjection.triameter_ge_of_evenLegTriangle` derives the
converse lower bound for arbitrary surjective edge-or-collapse maps from the
foot distances in Lemma 2.5(2) (p. 5). `DistanceProjection.triameter_le_indepNum`
is Corollary 5.1, inequality (5) (p. 11), extended to connected orders one
and two.
[Projection lemma](https://arxiv.org/html/2611.17259v1#S3.Thmtheorem2.2) ·
[Equality proof](https://arxiv.org/html/2611.17259v1#S4.p19.1) ·
[Model foot distances](https://arxiv.org/html/2611.17259v1#S2.Thmtheorem5) ·
[Independence bound](https://arxiv.org/html/2611.17259v1#S5.E5)

## Triage

### What the settlement shows

- Proved by `D5/S3/Combinatorics/Graph/Triameter/CliqueChains.question1`.
  The model determines whole cliques in G. If a block preimage contained a
  nonedge, the two endpoints and the lifted independent companions would
  give an independent set of size q(0)+q(1)+q(2)+2. The interfaces between
  consecutive cliques may use any nonempty set of edges between the indicated
  layers. The three lifted feet give the converse lower bound even for
  interfaces with a single edge. Any number of the three chains may be empty.
  The equivalence holds on all finite connected graphs, including orders one
  and two, where both sides are false.
- Literature scope. The source's Theorem 1.1 and Corollary 5.1 give the bound,
  the equality restrictions on the three triametral distances and the
  singleton-layer sharpness examples. Das–Abdioğlu, Theorem 4.3, covers the
  minimum-order family n = 2α + 1 through its classification at triameter
  2n−3. Kozerenko, Theorem 3.1(4), overlaps the α = 2 restriction to block
  graphs through its classification at triameter 7.
  [Literature findings](https://github.com/the-omega-institute/trureturing/issues/32242#issuecomment-7040984355)
- Open here. General positive-k equality remains open. Question 2 asks for
  the exact maximum triameter at fixed order and minimum degree. Question 3
  asks for analogues of Theorem 1.1 and Lemma 6.1 for the sum of distances
  among four or more prescribed vertices. The classification uses equality
  with the independence number and projection of three prescribed vertices.
  [Source questions](https://arxiv.org/html/2611.17259v1#S7)

## ASSUMED-UNVERIFIED

Worldwide priority remains unverified.
[Literature findings](https://github.com/the-omega-institute/trureturing/issues/32242#issuecomment-7040984355)
