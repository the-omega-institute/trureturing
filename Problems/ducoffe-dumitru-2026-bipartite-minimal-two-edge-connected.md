---
slug: ducoffe-dumitru-2026-bipartite-minimal-two-edge-connected
bibkey: ducoffe2026erdosgyarfas
doi: 10.48550/arXiv.2609.28594
url: https://arxiv.org/abs/2609.28594v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.result
---

# Minimal bipartite Erdős–Gyárfás counterexamples are 2-edge-connected

## Problem

Ducoffe–Dumitru, *Towards a more structured search for Erdős–Gyárfás
counter-examples*, arXiv:2609.28594v1, §1:

> for any class of graphs F, a counter-example within F refers to any graph
> G ∈ F such that G has minimum degree at least three but no cycle of length
> some power of two. It is called a minimal counter-example within F if it
> minimizes (|V(G)|, |E(G)|) with respect to the lexicographic order.

The bipartite clause in §6 reads:

> we also conjecture … that any minimal bipartite counter-example is 2-edge
> connected.

For a nonempty finite simple graph G, let HasPowTwoCycle(G) mean that G has
an IsCycle walk of length 2^k for a natural k ≥ 2. A bipartite
counterexample is a graph admitting a proper two-colouring, with degree at
least three at every vertex and no such cycle. Minimality compares
(|V(G)|, |E(G)|) lexicographically against every finite nonempty bipartite
counterexample, independently of its vertex type. The target conclusion
is that G is connected and deleting any edge of G leaves a connected
graph.

This is a structural question about potential counterexamples to Erdős
Problem #64, the Erdős–Gyárfás conjecture. It asserts neither that a
counterexample exists nor that every graph of minimum degree three has a
power-of-two cycle.

## Motivation

A structural restriction on minimal counterexamples reduces the graph
families that must be considered in the Erdős–Gyárfás problem. The
bipartite class is closed under the bridge contraction used below, after
reversing the colours on one component. The restriction removes bridges
without assuming the conjecture itself.

## Gap

The supplied v1 source explicitly presents the bipartite assertion as a
conjecture in §6. Its universal quantifiers range over every finite
nonempty bipartite counterexample that is lexicographically minimal, not
merely connected graphs or graphs on one fixed vertex type. The required
construction must preserve minimum degree, bipartiteness and every cycle
length relevant to the forbidden powers of two while reducing the vertex
count.

The supplied description of `formal-conjectures/ErdosProblems/64.lean`
concerns only Erdős Problem #64, whose status remains open; it is not a
statement or a resolution of this minimal-counterexample clause. No
exhaustive literature or priority determination is asserted.

## Route

First prove connectedness. If G has more than one connected component,
induce G on the vertex support of one component. This is nonempty and has
strictly fewer vertices. Every neighbour of a vertex lies in its own
component, so all degrees are preserved. Restrict a proper two-colouring.
An injective induced-graph inclusion maps every cycle back to G with the
same length. The induced graph is therefore a smaller bipartite
counterexample, contradicting minimality.

Now suppose uv is a bridge of the connected graph G. Deleting uv splits
G into components A and B, containing u and v respectively, whose vertex
supports partition V(G). Identify v with u and discard the edge uv.
The contracted graph H has vertex type V(G) minus {v}; all other edges
are the images of the original edges. No edge crosses between
A minus {u} and B minus {v}. In particular, u and v have no common
neighbour, so identification produces neither duplicate neighbours nor
loops.

Keep the original two-colouring on A and reverse it on B minus {v}.
The identified vertex receives the original colour of u. Since uv was a
properly coloured edge, each transferred edge incident to a former
neighbour of v is still properly coloured. Other edges lie entirely
inside one side, where keeping or reversing both endpoint colours
preserves inequality.

Every vertex other than the identified vertex retains its degree. The
identified vertex has degree deg_G(u) + deg_G(v) − 2 ≥ 4. Thus H still
has minimum degree at least three, and |V(H)| = |V(G)| − 1.

The identified vertex is the only possible passage between the two
sides. Every cycle of H lies entirely in A or entirely in
(B minus {v}) union {u}. To see this, rotate a cycle containing u so that
it starts at u. Its interior walk, obtained by removing the first and
last edges, avoids u because the cycle repeats no other vertex.
Adjacency preserves the side of every vertex in this interior walk,
so the entire interior lies on one side. A cycle avoiding u stays on one
side by the same adjacency argument.

On the A side, the inclusion into G maps the cycle back unchanged. On
the other side, send the identified vertex u back to v and keep every
other vertex fixed. Each side map is an injective graph homomorphism on
the corresponding induced graph. Mapping the cycle preserves IsCycle
and its exact length. Consequently every power-of-two cycle of H would
give one in G. H is a bipartite counterexample on fewer vertices,
contradicting minimality. The edge-count coordinate is retained in the
minimality definition, although both contradictions already use a
strict decrease in the vertex-count coordinate.

## Falsifier

The target would fail if a nonempty finite lexicographically minimal
bipartite counterexample were disconnected or contained an edge whose
deletion disconnected it. The proof route would fail if component
induction lost a neighbour, contraction identified two distinct
neighbours, the reversed colouring violated a transferred edge, or a
cycle crossed the identified vertex more than once. These are separate
obligations; a bound on cycle length would not replace the required
preservation of its exact length.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.result : claim`,
where claim quantifies over every finite vertex type and every minimal
bipartite counterexample. The complete settling module compiles
successfully with the pinned Lean toolchain. The final result's axiom
closure is `propext`, `Classical.choice`, `Quot.sound`. The source has no sorry, new axiom,
native_decide or retained diagnostic commands.

Pinned Mathlib supplies Walk.induce, Walk.map, Walk.length_map,
Walk.map_induce, Walk.IsCycle.of_map and Walk.IsCycle.map, together with
cycle rotation and nodup support lemmas. The generic cycle-confinement
argument supplies the side restriction needed by the length-preserving
cycle lift. The complete proof also constructs the new colouring and
neighbourhood injections and applies lexicographic minimality.

## Triage

`theorem`: the complete Lean proof establishes the target bipartite clause.
The settlement is a source-level formalization; no publication or generated
projection is claimed.

### What the settlement shows

- [proved: D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.result]
  Every minimal nonempty finite
  bipartite Erdős–Gyárfás counterexample is connected and stays connected
  after deletion of any one edge. The quantifiers retain the source's
  lexicographic minimality over all finite bipartite counterexamples.
- [source attribution] The supplied account of the paper's Corollary 2.2
  already gives 2-edge-connectivity for general minimal counterexamples.
  That assertion does not imply biconnectivity: deleting one vertex is
  a different operation from deleting one edge.
- [open] The general biconnectivity clause in the same §6 sentence is not
  settled by this proof. A graph may have no bridges and still possess a
  cut vertex.
- [open] The cubic biconnectivity clause in the same sentence is not
  settled by this proof. Bridge contraction creates a vertex of degree
  at least four, so the construction does not preserve cubicity and
  cannot supply the needed smaller competitor within the cubic class.
- [open] Erdős Problem #64 itself remains outside the conclusion.
  A conditional structural theorem about minimal counterexamples neither
  constructs such a graph nor rules out its existence.

## ASSUMED-UNVERIFIED

The quotations of §1, §2 and §6 were checked against the arXiv v1 text
(arXiv:2609.28594v1, 23 September 2026), the only listed version. The
literature reading covers searches by title, identifier, authors and the
phrases "minimal bipartite counter-example" and "2-edge connected", and
the file `ErdosProblems/64.lean` of google-deepmind/formal-conjectures,
which states only the main Erdős–Gyárfás problem; citation indexes for
the paper were unavailable, so a later independent settlement cannot be
excluded. No worldwide priority claim and no settlement of the
neighbouring biconnectivity clauses is asserted.
