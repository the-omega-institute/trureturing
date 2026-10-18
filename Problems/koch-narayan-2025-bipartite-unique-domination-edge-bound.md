---
slug: koch-narayan-2025-bipartite-unique-domination-edge-bound
bibkey: kochnarayan2025uniquedomination
doi: 10.48550/arXiv.2511.01719
url: https://arxiv.org/abs/2511.01719v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.result
---

# The Koch-Narayan bipartite edge bound is false

## Problem

Koch and Narayan, *Maximal bipartite graphs with a unique minimum dominating set*,
arXiv:2511.01719v1, Conjecture 1, assert |E(G)| <= m(n,gamma) for every finite
simple bipartite graph without isolated vertices, with a unique minimum
dominating set, gamma >= 2 and n >= 3gamma. With a=ceil(gamma/2),
b=floor(gamma/2), the exact printed expression is

    Phi = max(0,n-3gamma-2a-b+1),
    m = 2gamma+2ab+min(n-3gamma,2a-b+1)(2a+1)
        + sum(i=1,...,Phi) ((2a+1)+ceil(i/2)).

## Motivation

The theorem `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.result`
negates the whole universal claim. Its graph has 14 vertices, 28 edges and a
unique minimum dominating set of cardinality four, whereas m(14,4)=26.

## Gap

The source proves the ranges gamma=2 and n=3gamma. The counterexample has
gamma=4 and n=14>12. The source note records the bounded prior-resolution and
native-overlap scope; no exhaustive novelty or priority claim is made.

## Route

The four centers 0,7,8,9 have disjoint closed neighborhoods partitioning all
vertices. Every dominating set meets each block, so it has at least four members.
At cardinality four there is one member per block. The leaf 11 forces the first
choice into {0,11}, excluding the three common hubs. In each other block,
choosing one of its two noncenters leaves its partner undominated, so all three
other centers are selected. Choosing 11 instead of 0 then leaves 10 undominated.
Thus every minimum attaining set is exactly {0,7,8,9}. Native minimum attainment
and the native upper-bound lemma identify the domination number with four.

## Falsifier

The displayed graph would fail as a counterexample if a source hypothesis were
absent, another set of cardinality at most four dominated, its actual edge count
were at most 26, or the printed formula evaluated differently at (14,4).

## Evidence

The Lean result uses actual SimpleGraph adjacency, bipartiteness, absence of
isolates and edgeFinset cardinality. Its minimum and uniqueness arguments range
over all finite sets and are transferred to all sets by the finite Set/Finset
membership and cardinality equivalences. The arithmetic is over integers with
exact rational ceiling/floor and the inclusive integer interval from one to Phi.

## Triage

`theorem`; the result refutes Conjecture 1 as printed. The apparent Case 3 index
max(0,n-3gamma-2a+b-1) is also zero at (14,4), so changing only that index does
not remove the counterexample. The true extremal function, other corrected
conjectures, and the unrestricted predecessor question remain outside this result.

## ASSUMED-UNVERIFIED

The bounded literature screen cannot exclude an unindexed prior resolution.
Formal correctness does not certify world priority or the status of an
unspecified reformulation. Minimum cardinality is used throughout; no claim is
made about uniqueness among merely inclusion-minimal dominating sets.
