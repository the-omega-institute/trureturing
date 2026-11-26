---
slug: zheng-wu-2025-odd-line-spanning-trees
bibkey: zheng2025oddspanning
doi: null
url: https://arxiv.org/abs/2503.17676v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree.result
---

# Odd spanning trees of line graphs

## Problem

Jingyu Zheng and Baoyindureng Wu ask in §5(2), p. 17:

> More specifically, when does a line graph have an odd spanning tree?

This is the line-graph subquestion of §5(2).
[Primary text](https://arxiv.org/pdf/2503.17676v1#page=17)

The event concerns every finite undirected simple root graph $F$, including
roots with isolates and disconnected roots. An odd spanning tree of
$L(F)$ is a nonempty spanning tree in which all degrees are odd. Let
$m = |E(F)|$. The event asserts that such a tree exists exactly when $m$
is positive and even and the following partition condition holds.

At each vertex, partition its incident edges into nonempty blocks. Tag
each block by its root vertex, and join the two blocks of each original
edge at its two endpoints. The resulting graph $T$ must be a tree. At
every block $b$ of degree at least two, at least two connected components
of $T-b$ must have odd vertex cardinality. Isolates contribute empty
partitions. Both sides fail when $m=0$ or $m$ is odd.
[Exact event and preregistration](https://github.com/the-omega-institute/trureturing/issues/31442)

## Motivation

The criterion describes which root incidences can be separated into a
tree whose branch parities support local degree assignments. The same
incidence partitions serve as witnesses in both directions.

## Route

Given an odd spanning tree of the line graph, restrict its edges to each
endpoint clique. Each restriction is a forest, and its components give
the blocks at that endpoint. Two distinct edges of a simple root have at
most one common endpoint, so the local forests partition the spanning-tree
edges. The split graph is connected. The number of members summed over
all blocks is $2m$, and the local trees have $m-1$ edges in total. Thus
there are $2m-(m-1)=m+1$ blocks, and the split graph is a tree.

The line-tree degree at an original edge is a sum of two local
contributions. Exactly one is odd. Choose that block as the head of
the split edge. Each block receives an even number of heads by
handshaking in its local tree. Summing indegrees on the neighbor side of
a cut edge gives its branch order minus one, plus one if the cut edge
points into that side. It follows that the edge points toward the block
exactly when that neighbor branch has odd order. A nonsingleton local
tree has at least two leaves and therefore at least two odd vertices.

Conversely, orient the split tree by the same cut rule. Since it has an
even number of edges, the rule is consistent at both ends and makes
every indegree even. A singleton block uses the singleton tree. Every
larger block has a nonempty even incoming set. Give two marked members
the ends of a path, put the unmarked members in its interior, and attach
the remaining marked members as leaves at one end. The resulting tree
has exactly the desired odd-degree members.

Project the local trees to the original edge labels and take their
union. Split connectivity gives connectivity of the union. Distinct
local trees have disjoint edge sets, so the union has $m-1$ edges and is a
spanning tree. Each original edge gets its odd contribution at the
chosen head.

## Falsifier

A finite simple root graph with exactly one side true refutes the
preregistered event. The typed statement tests both directions on the
same root. A characterization assuming root connectivity, deleting root
edges or requiring an odd branch at every leaf would change the event.

## Evidence

`D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree.result` is a
kernel-checked equivalence over the original root and its line graph.
`EndpointSplit` represents the partitions, and `TreeParity` supplies the
orientation and local odd-degree realization. The source uses the two
sealed constructive directions and Mathlib's actual edge, line graph,
tree and induced-component types.

## Gap

The main result, both incidence counts and the three tree-parity
theorems have source-bound §3.9 registrations. Four endpoint-split
helper audits remain open. The source checker rejects the
split-pair membership registration at
`source.dictionary_or_proof_coordinate` because its dependent
parameter is a family of setoids. The other three helpers still
need lawful readouts for block nonemptiness and the two connectivity
transfers. Canonical freeze and repository checks require the
integration worktree.
[Issue #31442](https://github.com/the-omega-institute/trureturing/issues/31442)

## Triage

### What the settlement shows

**Proved.** `D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree.result` ties existence to a split of actual endpoint incidences and the parities of its vertex-deletion components. A disconnected root remains in scope. Only its edge-bearing part contributes line-graph vertices.

**Literature.** Xu and Xu's Theorem 2.4 gives the exact odd-tree count from
the spanning-tree degree polynomial. Zhou and Bu's Theorem 6.12 supplies
a line-graph enumerator from the root, and Remark 6.13 discusses the
endpoint clique partition. The screened texts supply exact algebraic
tests and enumeration. The structural criterion here gives a partition
witness and an explicit reconstruction from it.
[Xu and Xu](https://arxiv.org/abs/2602.08179) ·
[Zhou and Bu](https://doi.org/10.1007/s10801-020-00969-w)

**Open here.** The general connected claw-free characterization and
the other questions of §5 lie outside the line-graph settlement. The
formal proof gives existence and does not bound the complexity of finding
a qualifying split.

## ASSUMED-UNVERIFIED

Unindexed and inaccessible full texts remain outside the literature
comparison. The searches attached to the preregistration establish a
bounded literature reading.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/31442)
