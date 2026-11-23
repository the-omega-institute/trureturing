---
slug: ugurlu-2026-fixed-budget-nc-transfers
bibkey: ugurlu2026objectivetransfer
doi: 10.48550/arXiv.2609.34394
url: https://arxiv.org/abs/2609.34394v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/VertexDeletion/Classification.result
---

# Fixed-budget transfers involving NC on trees and bounded-degree graphs

## Problem

Section 9 asks “whether the constants improve on trees or on bounded-degree
graphs, or whether the NC directions remain vanishing there.” The selected
clause fixes an exact budget $b\ge 2$ and allows the order $n>b$ to vary.
For positive component sizes $c_1,\ldots,c_m$ of the induced survivor graph,
the damage scores are $NC=m-1$, $PC=\binom n2-\sum_i\binom{c_i}{2}$, and
$LCC=n-\max_i c_i$. A transfer is defined on graphs whose selected target
optimum is positive. Its optimistic score selects the best target score over
all exact source optimizers.

[Versioned question](https://arxiv.org/html/2609.34394v1#S9.p1) · [Preregistration](https://github.com/the-omega-institute/trureturing/issues/33528)

## Motivation

Component count rewards each additional component equally. Pairwise and
largest-component damage depend on their sizes. Trees and degree bounds let
one distinguish the effect of component multiplicity from the effect of
balancing the surviving mass.

## Gap

Section 7.4 gives vanishing for the four NC directions over connected graphs.
Its apex construction leaves the tree class. The source and literature sweep
in the preregistration found no equivalent fixed-budget restricted-class
classification.

## Route

Take a spine with $b$ alternating hubs, attach $k$ leaves to each hub, and
append a long tail. Deleting the hubs gives the unique NC optimum. Deleting
appropriately spaced tail vertices realizes $b+1$ components of equal size
and uniquely optimizes PC and LCC. Reachability and a count of surviving
positive tail runs prove that other cuts have strictly weaker profiles.
For the inbound degree bound, charge every survivor component outside the
root component to a deleted vertex by choosing a survivor closest to a
surviving root. Each deleted vertex has a closer neighbor, leaving at most
$\Delta-1$ available charges. For degree at most two, take a spanning linear
order with an optional closing edge and realize the maximal feasible number
of balanced positive runs.

## Falsifier

For some fixed $b\ge 2$, a positive lower bound on the largest of the four
worst-tie ratios over the eligible trees would disprove simultaneous
vanishing. A connected graph with $n>b$, maximum degree at most $\Delta\ge3$,
and positive NC optimum would refute the incoming bound if one exact PC or
LCC optimizer had NC ratio less than $1/[b(\Delta-1)]$. A positive lower
bound on either positive-target optimistic ratio over the eligible subcubic
trees would refute its zero infimum. On a connected graph of maximum degree
at most two with $n>b$, the absence of a common exact optimizer or an
ordered optimistic ratio below one on a positive-target domain would refute
the last clause.

## Evidence

The score and tie conventions come from [versioned §2](https://arxiv.org/html/2609.34394v1#S2).
The Lean theorem `Ugurlu33528.result` in
`D5/S3/Combinatorics/Graph/VertexDeletion/Classification.lean` combines
`uniform_tree_simultaneous_epsilon`, `bounded_degree_transfers_into_nc`,
`subcubic_tree_optimistic_out_of_nc_infimum_zero`, and the two degree-two
optimizer and transfer theorems. The component count uses the actual induced
survivor graph. In the degree-three construction each hub has one leaf.
Increasing the tail length gives simultaneous pointwise upper bounds on the
two outgoing ratios, so taking the best target score among exact NC optimizers
still yields zero infimum for each positive-target domain.

## Triage

### What the settlement shows

- **Proved.** For each $\varepsilon>0$ one tree with all three target optima
  positive gives all four NC transfer ratios below $\varepsilon$, simultaneously
  and for every tied source optimizer.
- **Proved.** At fixed maximum degree bound $\Delta\ge3$, every exact PC or
  LCC optimizer has transfer ratio into NC at least $1/[b(\Delta-1)]$
  whenever the NC optimum is positive.
- **Proved.** Both optimistic transfers out of NC have infimum zero already
  on trees of maximum degree at most three. Each infimum ranges over its own
  positive-target domain.
- **Proved.** In the connected degree-at-most-two class, a common exact
  optimum exists. Every ordered optimistic ratio equals one when its target
  optimum is positive. The common optimizer uses $\min(n-b,b+1)$ balanced
  runs in a path and $\min(n-b,b)$ in a cycle.
- **Open.** Sharp positive constants into NC at fixed bounds $\Delta\ge3$,
  the corresponding proportional-budget behavior, and the distinct
  PC–LCC constant question on restricted classes.

The public theorem escape audits remain unfinished under §3.9.
[Registration issue](https://github.com/the-omega-institute/trureturing/issues/33626)

## ASSUMED-UNVERIFIED

The recorded literature search does not establish that no earlier
equivalent restricted-class classification exists. Sharp incoming constants
for fixed bounds above two, proportional budgets, and sharp PC–LCC
constants on restricted classes remain outside the proved statement.
The linked four-slot escape registration remains unfinished.
