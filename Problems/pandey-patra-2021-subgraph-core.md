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

## Resolution and limits

The exact statement is proved by
`D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.result`, with direct
reuse of the existing De–Patra counting modules. No induced-only, spanning-only,
single-maximizer, subclass, or order-cutoff statement is substituted. The
formal axioms are the standard `propext`, `Classical.choice`, and `Quot.sound`
closure reported for the source modules.

This dossier records one external problem and its formal resolution. It makes
no claim about priority, originality, worldwide openness, or solved credit.
The two new public theorem Reg audits are unfinished and remain covered only by
the precise linked-issue exception at
https://github.com/the-omega-institute/trureturing/issues/23700#issuecomment-6499492075;
the exception permits delivery and is not registration evidence.
