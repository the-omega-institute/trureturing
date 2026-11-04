---
bibkey: pandeypatra2021subgraphcore
authors: Dinesh Pandey; Kamal Lochan Patra
year: 2021
title: "Some new central parts of connected graphs"
doi: null
url: https://arxiv.org/abs/2110.00738v1
claim: "Conjecture 3.25 states that the subgraph core of every finite simple connected graph is contained in one block."
strata_touched:
  - D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock
license: citation-only
triage: anchor
---

# The subgraph core conjecture for connected graphs

## Verified locator

Dinesh Pandey and Kamal Lochan Patra, *Some new central parts of connected graphs*,
arXiv:2110.00738v1, https://arxiv.org/abs/2110.00738v1 and
https://arxiv.org/pdf/2110.00738v1. The paper's page 1 fixes finite simple
connected undirected graphs, cut vertices and blocks. Definition 3.23 on page 9
counts connected subgraphs containing a vertex, and Conjecture 3.25 on page 9
states that the subgraph core is contained in a block.

## Native statement

For a graph G, f_G(v) is the number of actual connected subgraphs containing v,
with each subgraph retaining its vertex and edge choices. The subgraph core is
the set of vertices maximizing f_G. A block is a maximal connected subgraph
without a cut vertex under the native subgraph convention. The formal result
keeps singleton graphs, bridge edges, empty deletion, and every finite order;
it adds no cutoff and does not replace the count by induced or spanning
subgraphs.

## Formal resolution

`D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock.result` proves the exact
whole statement. Its proof uses the existing De–Patra connected-subgraph
counting interfaces, an attachment injection for subgraphs omitting a root,
an exact one-root gluing inequality, and the path hull of all maximizers.
`SubgraphCoreHull.exists_no_cut_cover` is a consumed helper for that proof and
is not a second external problem or a separate resolution claim.

The result is a repository formalization of this one cited conjecture. It makes
no priority, originality, worldwide-openness, or empirical claim. The public
Reg escape audits for the two new declarations remain unfinished under the
precise linked-issue exception recorded at
https://github.com/the-omega-institute/trureturing/issues/23700#issuecomment-6499492075;
that exception is not registration evidence.
