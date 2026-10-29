---
slug: pandey-patra-2021-subgraph-core
bibkey: pandeypatra2021subgraphcore
doi: null
url: https://arxiv.org/abs/2110.00738v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.result
---

# Pandey–Patra subgraph core conjecture

## Problem

Dinesh Pandey and Kamal Lochan Patra, *Some new central parts of connected
graphs*, arXiv:2110.00738v1, Conjecture 3.25, page 9:

> The subgraph core of a graph G is contained in a block of G.

The native domain is every finite simple connected undirected graph. The
subgraph number counts all actual connected subgraphs containing a vertex,
including singleton subgraphs and distinct edge choices. The conclusion is one
native maximal no-cut block containing the entire set of maximizing vertices.
Singleton, bridge-edge, empty-deletion, and unbounded-order cases remain in
scope.

## Motivation

Conjecture 3.25 asks whether the vertices maximizing the number of connected
subgraphs containing a vertex share one native block. The formal result settles
that whole question while retaining the source's actual subgraph carrier and
its maximal-block convention. The cited Library note is
[`D5/L/Geometry/pandeypatra2021subgraphcore`](../Library/Geometry/pandeypatra2021subgraphcore.md);
the note's `strata_touched` entry remains the owning graph-invariant module.

## Gap

Before this resolution, the cited paper stated the containment assertion as
Conjecture 3.25. The remaining publication boundary is documentary: the
formal source and frozen records already identify the exact theorem, while the
two public theorem Reg audits remain unfinished under the linked-issue
exception recorded below.

## Route

`SubgraphCoreBlock.subgraphNumber` uses the existing `countContaining` carrier,
so it preserves both vertex and edge choices. `subgraphCore` is the complete
maximizer set, and `NativeBlock` expresses native no-cut connectivity together
with maximality under actual subgraph inclusion. The proof first bounds
root-omitting subgraphs by an attachment injection, then uses exact one-root
gluing to exclude maximizers in different deletion components. The union of
all simple paths between maximizers has no cut vertex; finiteness extends it to
a maximal native block. The path-hull lemma is a consumed helper, not another
problem.

## Falsifier

This resolution would fail to answer the source question if the formal carrier
counted only induced or spanning subgraphs, if it selected only one maximizer,
if `NativeBlock` weakened native maximality or deletion, or if the proof
excluded singleton, bridge-edge, empty-deletion, or some finite order. It would
also fail if the path-hull helper were asserted as a separate external problem.
The delivered statement makes none of those substitutions.

## Evidence

The exact statement is proved by
`D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.result`, with direct
reuse of the existing De–Patra counting modules. No induced-only, spanning-only,
single-maximizer, subclass, or order-cutoff statement is substituted. The
formal axioms are the standard `propext`, `Classical.choice`, and `Quot.sound`
closure reported for the source modules.

The consumed helper
`D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreHull.exists_no_cut_cover`
constructs the path hull used by the block proof; it is not a second external
problem. The proof's live path uses the attachment injection, exact one-root
gluing, deletion-component separation, and the union of all simple paths
between maximizers.

## Triage

`theorem`; this is one named external problem and one typed
`OpenProblemResolutionClaim(Proved)`. The settlement proves the full native
quantifier and supplies one shared maximal no-cut block for the complete
maximizing set. It does not claim priority, originality, worldwide openness,
or solved credit. No experimental program or numerical certificate is used;
the utility classification is `none` because the delivered mathematics is a
general symbolic graph construction.

The two new public theorem Reg audits are unfinished and remain covered only by
the precise linked-issue exception at
https://github.com/the-omega-institute/trureturing/issues/23700#issuecomment-6499492075;
the exception permits delivery and is not registration evidence.

## ASSUMED-UNVERIFIED

The dossier does not establish that the source's historical wording was still
open worldwide beyond the pre-registered literature reading, and it makes no
priority or originality claim. The linked Reg exception is unfinished audit
evidence, not a declared validation. The formal theorem, source locator, and
native boundary statements above are the delivered scope.
