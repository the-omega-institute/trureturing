---
slug: gurvich-krnc-milanic-vyalyi-2026-leaf-root-edge-deletion
bibkey: gurvich2026noninduced
doi: 10.48550/arXiv.2611.06636
url: https://arxiv.org/abs/2611.06636v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.result
---

# Conjecture 6.4 on deleting a leaf root edge

## Problem

Vladimir Gurvich, Matjaž Krnc, Martin Milanič, and Mikhail Vyalyi state
Conjecture 6.4 in Section 6 of *Non-induced inherent graphs*, page 21.

> Let (H, s, t) be a two-rooted inherent graph such that s ≠ t, d_H(s) = 1, and let H′ be obtained from H by deleting the unique edge incident with s. Then (H′, s, t) is inherent.

[Conjecture 6.4](https://arxiv.org/pdf/2611.06636v1#page=21)

The closed proposition quantifies over every finite simple graph and ordered
distinct roots with first degree at most second degree. For the unique neighbor
u of the first root, deletion removes the single unordered edge {s,u} and
retains the vertex set and the ordered roots. The condition that adjacency to s
is equivalent to equality with u expresses degree one.

The inherence predicate quantifies over every finite simple host, including
disconnected hosts and the empty host. It requires an avoidable copy whenever
the host contains a copy. Copies are injective adjacency-preserving maps.
Each extension consists of two distinct endpoints outside the whole range
with the specified root adjacencies. An avoidable copy admits a walk between
the endpoints of each such extension in the graph induced outside its range.
Reachability there is equivalent to existence of a path there. A copy with
zero extensions is avoidable. Relabeling finite carriers by Fin of their
cardinality preserves these conditions. [Definitions](https://arxiv.org/pdf/2611.06636v1#page=4)

## Motivation

Proposition 6.3 gives the deletion property for paths rooted at both endpoints.
Conjecture 6.4 asks whether a leaf first root suffices. An internal second root
permits a containing host to confine the deleted pattern. [Source](https://arxiv.org/pdf/2611.06636v1#page=21)

## Gap

Theorem 3.1 gives inherence for the intact path as the type-I comb with parameters
4, 0 and 2. The new step is confinement of the deleted pattern. It requires an
extension in every copy, with both endpoints outside the range of that same copy
and with no path between them there. The literature screen recorded in the
preregistration found no earlier settlement in the versioned source, the two
predecessors and the available index records it examined. [Theorem 3.1](https://arxiv.org/pdf/2611.06636v1#page=10) · [Preregistration and search scope](https://github.com/the-omega-institute/trureturing/issues/33823)

## Route

For the six-vertex path on 0 through 5, roots 0 and 3 have degrees one and
two, and the neighbor of root 0 is vertex 1. A containing copy lies in a single
connected component. In that component, the proof specializes the maximal
connected set argument of Lemma 3.4. A maximal connected set disjoint from
some copy forces every exterior boundary vertex into every copy disjoint from
that set. Shifting and rerouting the path then gives a copy without extensions,
or a copy whose exterior endpoints are in the connected set. The resulting
avoidability transports from the component to the host. [Lemma 3.4](https://arxiv.org/pdf/2611.06636v1#page=12)

## Falsifier

After deletion, use the nine-vertex tree with center 0 and arms (0,1,2),
(0,3,4), (0,5,6) and (0,7,8). The tuple (5,2,1,0,3,4) is a copy in pattern
vertex order. In every copy, the path on pattern vertices 1 through 5 uses two
full arms, with the second root at the center. The first root occupies a third
arm. The other vertex of that arm and the unused fourth midpoint are fresh,
distinct extension endpoints in root order. The first has no neighbor outside
the range of the copy, so this extension cannot close.

## Evidence

The Lean theorem `GurvichLeafRootEdgeDeletionRefutation.result` has type
`Not GurvichLeafRootEdgeDeletionRefutation.claim`. The closed definition uses
the native graph copy, edge deletion, induced graph and reachability
operations. The proof uses the uniform intact-path theorem, the displayed
deleted-pattern copy and the all-copy isolation theorem. The claim statement
identity is `sha256:11687bbbfc5d04e0d441f9f4013eae270b876d3869a54b3b1a440fc41d370e03`.
The result identity is `sha256:9f42f2e42a3a6bab1f562f6d7f24e4dec4fcc41eec228974ff9483856a57beb7`.
The axiom closure is `Classical.choice`, `Quot.sound` and `propext`.
The source is attributed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Triage

Tier 1 under the external named open problem route. The four-arm tree is a
certified instance with a typed refutation of the complete implication.
The only public theorem is the designated refutation, which is exempt from
four-slot registration. The result leaves the both-endpoint case of
Proposition 6.3 intact. [Issue #33823](https://github.com/the-omega-institute/trureturing/issues/33823)

## ASSUMED-UNVERIFIED

Worldwide priority and complete coverage of subsequent work are unverified.
The claim uses the finite convention of the source's arguments and its
adapted predecessor. Infinite hosts are outside the statement.
[Adapted predecessor](https://doi.org/10.37236/13023)
