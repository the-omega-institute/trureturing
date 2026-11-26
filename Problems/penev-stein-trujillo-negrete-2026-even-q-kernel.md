---
slug: penev-stein-trujillo-negrete-2026-even-q-kernel
bibkey: penev2026small
doi: 10.48550/arXiv.2608.00825
url: https://arxiv.org/abs/2608.00825v1
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination.IsDominating
---

# The even-radius extension of the small q-kernel bound

## Problem

Irena Penev, Maya Stein, and Ana Trujillo-Negrete, *Small $q$-kernels in
digraphs*, pose the following question immediately after Theorem 1.6.

> We do not know whether Theorem 1.6 also holds if $q$ is even.

Theorem 1.6 gives the bound $|Q|\le |V(D)|/(q+1)+1$ for odd integers
$q\ge3$ in a source-free bipartite digraph with an out-branching.
[Exact question](https://arxiv.org/html/2608.00825v1#S1.p12.1) · [Theorem 1.6](https://arxiv.org/html/2608.00825v1#S1.Thmtheorem6)

The preregistered assertion quantifies over every even natural $q\ge4$
and every finite loopless digraph $D$ whose underlying simple graph is
bipartite. Its hypotheses are that every vertex has an incoming arc and
that $D$ contains a spanning out-arborescence, a rooted spanning tree
whose arcs point away from the root. At most one arc is allowed in each
ordered direction, and opposite arcs may coexist. The conclusion is that
there is an independent vertex set $Q$ such that every vertex is reached
from some vertex of $Q$ by a directed path of length at most $q$, including
paths of length zero, and
$ (q+1)|Q|\le |V(D)|+q+1 $. Independence and reachability use all the
arcs of $D$. The preregistered endpoint preserves $q\ge3$ after imposing
evenness. A counterexample at $q=4$ also answers the printed question
under the reading that additionally includes $q=2$.
[Definition in the introduction](https://arxiv.org/html/2608.00825v1#S1) · [Digraph conventions](https://arxiv.org/html/2608.00825v1#S2) · [Preregistration #31451](https://github.com/the-omega-institute/trureturing/issues/31451)

## Motivation

Ordinary domination on a finite simple graph, represented by the frozen
`SimpleGraph.IsDominating`, is the radius-one reachability condition
when edges are read in both directions. The paper adds independence and
uses outward reachability on directed arcs. In its odd-$q$ proof,
depth residues modulo $q+1$ lie in single bipartition classes because the
modulus is even. Applying Theorem 1.6 at $q-1$ yields the weaker even-radius
bound $|V(D)|/q+1$.
[Proof of Theorem 1.6](https://arxiv.org/html/2608.00825v1#S5)

## Gap

The Tier 1 preregistration records the exact question, quantified event,
and bounded literature and repository screens before the probe. The
reported general counterexamples with an odd directed cycle cannot meet
bipartiteness. The known stronger radius-two result for source-free
unicyclic orientations concerns a restricted class. The recorded searches
found no prior resolution of the stated extension in the sources inspected.
[Preregistration and source screens](https://github.com/the-omega-institute/trureturing/issues/31451)

## Route

Let $q=4$ and take the 29 vertices $0,1,\ldots,28$. Use exactly the arcs
listed below. Every arrow in a chain is an arc.

| Part | Arcs | Count |
| --- | --- | ---: |
| Directed cycle | $0\to1\to2\to3\to4\to5\to0$ | 6 |
| Entry to the hub | $0\to6$ | 1 |
| Short branch | $6\to7\to8\to9\to10$ | 4 |
| First long branch | $6\to11\to12\to13\to14\to15\to16\to17\to18\to19$ | 9 |
| Second long branch | $6\to20\to21\to22\to23\to24\to25\to26\to27\to28$ | 9 |
| Return arcs | $15\to6$, $24\to6$ | 2 |
| Total | | 31 |

Color the cycle alternately and color each branch by depth from $6$.
The color class containing $0$ is
$\{0,2,4,7,9,11,13,15,17,19,20,22,24,26,28\}$, and its complement
is the other class. Both return arcs go from depth five into the hub,
so each crosses the bipartition. Every vertex has an in-neighbor. Deleting $5\to0$, $15\to6$,
and $24\to6$ leaves a spanning out-arborescence rooted at $0$.

No arc from outside enters the six-cycle, and a single cycle center reaches
at most five cycle vertices within four steps. Thus every $4$-kernel uses
at least two cycle centers.

With the hub omitted, the demands $10,14,23,19,28$ must be reached by
centers in the five disjoint intervals $[7,10]$, $[11,14]$, $[20,23]$,
$[15,19]$, and $[24,28]$, respectively. Reaching a depth-four demand
through the hub from another center costs at least five arcs. The two
terminal demands are each nine arcs from the hub. This forces five
off-cycle centers.

With the hub selected, the demands $15,19$ have predecessor intervals
$[11,15]$ and $[15,19]$ at radius four. Their unique common candidate is
$15$, barred by $15\to6$. Similarly, the demands $24,28$ have intervals
$[20,24]$ and $[24,28]$ with common candidate $24$, barred by $24\to6$.
Both pairs therefore require two centers on their own branches. Counting
the hub gives five off-cycle centers again. The minimum is seven, attained
by $\{0,2,7,11,16,20,25\}$.

## Falsifier

The preregistered universal assertion is false if one admissible graph at
one even $q\ge4$ has no independent radius-$q$ cover within the bound. For
the displayed graph the bound is $5|Q|\le34$, so at most six centers are
allowed. The required lower bound $|Q|\ge7$ gives $5|Q|\ge35$.

## Evidence

The Lean result names the negation of the full quantified claim. Mathlib's
directed adjacency represents each ordered arc. The spanning subgraph
uses Mathlib's arborescence structure, and the cover is stated with
vertex-simple directed paths in the ambient digraph. For the
counterexample, the proof computes bounded predecessors recursively
from incoming arcs and proves their correspondence with bounded walks.
Every bounded path gives such a walk. Finite kernel decisions verify the
cycle and predecessor facts. The counting argument applies to an
arbitrary independent cover.

The witness also has no opposite arcs, so it lies in the more restrictive
class of oriented graphs. The minimum of seven is for the displayed
graph at radius four. [Lean source](../D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation.lean)

## Triage

The theorem-level refutation instantiates the universal statement at
$q=4$. The contradiction uses the complete digraph in **Route**.

## ASSUMED-UNVERIFIED

Unpublished and unindexed prior work and the full Wang–Deng–Chen text
remain outside the preregistration's literature coverage. The scoped
search leaves literature priority unresolved.
[Preregistration and source screens](https://github.com/the-omega-institute/trureturing/issues/31451)
