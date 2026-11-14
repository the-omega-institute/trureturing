---
slug: boldi-vigna-general-sweep-endpoints
bibkey: boldi2026sweep
doi: 10.48550/arXiv.2610.41385
url: https://arxiv.org/abs/2610.41385v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SweepDimension/Endpoints.result
---

# General finite-poset sweep dimension and the two width endpoints

## Problem

Paolo Boldi and Sebastiano Vigna, arXiv:2610.41385v1, Section 6, second closing bullet:

> The sweep dimension of specific posets. We have computed the sweep dimension of chains, antichains and complete bipartite posets.

The same bullet asks to characterize the posets for which sweep dimension attains
the lower bound max(2,width) or the upper bound twice the width.

For a finite poset P, an interval means any order-convex subset, including empty
and full subsets. A k-sweep system is a family of k arbitrary linear orders,
with repetitions allowed, satisfying: for every interval I and every y outside I,
some family order puts y before every x in I. The orders need not extend P.
Sweep dimension is the least such k. Theta is the largest cardinality of a subset
containing no strict three-chain a < b < c.

The complete general question is to prove s(P)=theta(P), and for every P with at
least two points to characterize both endpoints. The lower endpoint holds exactly
for chains and antichains. The upper endpoint holds exactly when two disjoint
maximum-cardinality antichains exist.

## Motivation

`D5/S3/Combinatorics/SweepDimension/Endpoints.result` states the identity and both
equivalences for every finite poset with at least two points. The identity itself
is also established for empty and singleton carriers under the natural-number
minimum convention. This does not extend the source endpoint proposition to them.

## Gap

Preregistration: https://github.com/the-omega-institute/trureturing/issues/30201.
The bounded source and all-state ownership checks found the general endpoint
question here and the separately owned product/Boolean question in issue 25960.
This is not a claim that all literature has been searched or of global priority.
Classical Dilworth and Sperner methods are not themselves new resolutions.

## Route

1. A maximum three-chain-free subset assigns a distinct sweep order to each point:
   the convex hull of the remaining points omits that point.
2. An antichain in P times the two-element chain projects injectively to a
   three-chain-free subset of P. Thus the product width is at most theta.
3. The finite Dilworth supplier covers the product by at most theta chains.
   For each chain, put its lower-layer points first in descending order, then
   the remaining upper-layer points in ascending order, then all other points.
   A common point is automatically first among lower-layer points. Extend the
   resulting block partial order to a linear order. Convexity gives the two cases.
4. A three-chain-free subset splits into minimal and nonminimal antichains.
   Their cardinalities characterize equality at twice the width.
5. A proper maximum antichain can be enlarged by an outside point without creating
   a strict three-chain. Width at least two therefore forces strict inequality
   at the lower endpoint unless the whole poset is an antichain. Width at most
   one gives the chain case.

## Falsifier

A mismatch in the interval or order quantifiers, a failure of either block order
case, or a finite poset contradicting either endpoint equivalence would falsify
the proposed answer. The Lean statement retains the universal carrier and partial
order and the original at-least-two-points hypothesis for both endpoints.

## Evidence

The result is carried by the Lean declarations and their axiom closure, not by
this dossier. Independent semantic admission and integration are separate duties.
The whole-domain typed Reg attempt is not machine-validated: the current
extractor rejects its rigid universe parameters. The exact unfinished audit
targets and required evidence are tracked in
https://github.com/the-omega-institute/trureturing/issues/30231 under CLAUDE §3.9.

## Triage

Proved: the complete general endpoint result is formalized. The decisive
structure is the maximum size of a union of two disjoint antichains, equivalently
the maximum size of a three-chain-free subset. This identifies both extremal
width cases; the identity also handles the empty and singleton carriers, while
the source endpoint assertion keeps its at-least-two-points hypothesis.

Unresolved here: products of chains and Boolean
lattices remain with issue 25960. Tree recurrences, the lambda second-term question,
and staircase-region classification are outside this result. No external problem
credit follows from a partial theorem, a supplier theorem, or this dossier alone.

## ASSUMED-UNVERIFIED

The bounded literature and ownership search does not establish global novelty.
