---
slug: alikhani-griswold-2026-connected-minus-four-family
bibkey: alikhanigriswold2026integerdominationroots
doi: 10.48550/arXiv.2608.00109
url: https://arxiv.org/abs/2608.00109v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result
---

# Connected graphs with ordinary domination root minus four

## Problem

Saeid Alikhani and Max Griswold, *On the Integer Domination Root Conjecture*,
arXiv:2608.00109v1, Section 4 item 3 asks:

> Does there exist an infinite family of graphs G satisfying D(G, -4) = 0?

The source uses finite simple undirected connected graphs. For ordinary
domination, a subset S dominates when each vertex belongs to S or has a
neighbor in S. The polynomial counts each such subset exactly once:

$$D(G,x)=\sum_{S\text{ dominates }G}x^{|S|}.$$

The exact result is: for every natural N there exist n>N and a simple graph G
on Fin n such that G is connected and D(G,-4)=0. Unbounded orders ensure
infinitely many isomorphism classes. Connectedness applies to G; the
dominating subsets need not themselves be connected. There is no additional
degree, planarity, cyclomatic-number, or root-multiplicity hypothesis.

The declaration is
`D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result`.
Its ordinary dominating subsets are exactly `DominatingSetAverage.domSets`;
the summands are integer powers of the integer minus four. Both existential
witnesses follow the universal N, and the inequality is strict.

## Motivation

The source's Theorem 2.1 already supplies a graph G33 with 33 vertices and
36 edges whose domination polynomial has a factor x+4. That finite example
is prior art. The question requires a construction of unbounded order.
The existing decreasing-predecessor connectedness theorem supplies paths in
the base graph without a second connectivity proof or a renamed supplier.

## Gap

The infinite-family conclusion follows from a root-preserving support
replication operation. The result does not assert that the chosen base is
smallest, classify all connected graphs with this root, establish any other
integer root, or constrain the family's cycle rank or maximum degree.
These are independent questions outside the delivered statement.

## Route

The general `Decomposition` interface permits arbitrary dimensions n,k,m,
dependent branch sizes, a graph, vertex labels, roots, incidence data and an
integer weight x. It imposes the exact local neighbor and leaf conditions.
Restriction to the core and branch subsets is inverse to disjoint assembly.
Cardinality adds, ordinary domination becomes internal branch domination
plus coverage of the core, and the weighted sum factors into exact
root-conditioned branch messages. This proves `reassembly`; substituting a
table whose entries are those same messages gives `zero_of_messages`.

The actual application uses G33, the four-cycle core 0,1,2,3, and eight
branches of sizes 2,2,2,2,6,3,3,9. At x=-4, the selected-root messages are
(12,12,12,12,972,-36,-36,-20736); the omitted-root messages are
(-4,-4,-4,-4,-1024,16,16,5888). The exact same decomposition supplies the
graph laws, message equalities and covered-core cancellation. None of these
numeric premises is left assumed. The resulting evaluation of G33 is zero.

Vertex 5 has exactly vertex 4 as its neighbor. For r copies of G33, join
each copied support 4 to a new hub and attach one pendant to the hub.
The weighted evaluation of the resulting graph is

$$x(x+2)D(G33,x)^r.$$

At x=-4 this vanishes for every r>=1. Paths through each support and the
hub prove connectedness. The graph has 33r+2 vertices, so r=N+1 gives
33(N+1)+2>N. Transport by a finite equivalence gives the required Fin n
vertex type. The case r=0 is K2 and its value at -4 is 8; it is not a
zero-valued member of this family.

## Falsifier

A mismatch between the ordinary dominating-subset sum and a connected-subset
variant, an unproved table entry, a failed graph law, a disconnected family
member, or a bounded-order construction would fail this exact statement.
The finite base alone would not settle it. The general checker requires
its message table and cancellation to refer to the same graph and weight.

## Evidence

The exact universal theorem, its general reassembly checker and its actual
application have current scoped Lean kernel evidence with only
Classical.choice, Quot.sound and propext, and no sorryAx. Both retained Reg
sources compile; compiled family evidence is distinct from completed
four-slot registration. The root and all dimensions in the public formulas
match the typed Lean statements.

The finite G33 and its reported root are attributed to Theorem 2.1 of the
source. The restriction/reassembly argument and support-family application
are repository synthesis. The note cites v1 and retains citation-only
use of the arXiv source; no author code or substantial source prose is
reproduced. The licensed source material is not assigned an invented
Creative Commons or publisher license.

## Triage

This is the complete unbounded connected-family result, not a finite-order
test or a result about connected dominating subsets. Its external
open-problem-resolution basis is issue
[#25087](https://github.com/the-omega-institute/trureturing/issues/25087).
The result's exact statement identifier is
`sha256:faa4a52a3fd8fb6f55ca09475a596c68a98037e568e5045f172a5e46bb6a4eb1`.
Every auxiliary theorem in the new host is used on the derivation path;
the family result supplies the external settlement basis without claiming
an independent escape witness for those organizational helpers.

## ASSUMED-UNVERIFIED

The bounded prior source screen found no exact later resolution on its
checked surfaces. Literature completeness and worldwide priority remain
ASSUMED-UNVERIFIED; absence in that screen does not establish global
nonresolution or originality.

Four public escape audits remain unfinished and disclosed at
[#25087, comment 6553848217](https://github.com/the-omega-institute/trureturing/issues/25087#issuecomment-6553848217):
`MinusFourReassembly.reassembly`, `MinusFourReassembly.zero_of_messages`,
`MinusFourReassembly.result`, and the original
`ConsecutiveCycleSumsGraph.connected_of_predecessor`. The first two have
compiled typed family evidence; the prior result-host Contract discovery
failed with `contract.discovery:rigid_universes` at `registration_1`, and
the second binding was not reached. The result retains its unfinished
exact bridge/family/Contract boundary. The supplier has compiled full
telescope family evidence but no Contract wrapper; no rigid-universes
failure is attributed to it. Lawful enrollment, enrolled readout,
sourceSelection reconstruction and current binding evidence are missing;
none is declared_validated. The existing linked-issue exception permits
delivery while keeping these obligations explicit.
