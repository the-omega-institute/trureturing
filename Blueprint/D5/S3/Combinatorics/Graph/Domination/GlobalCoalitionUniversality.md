# An obstruction to global coalition universality

## Abstract

The edgeless two-vertex graph has no global coalition realization, because every partition block has an actual coalition partner.

Anholcer, Besharati, Mojdeh and Samadzadeh, Global coalitions in graphs, arXiv:2509.15386v4, Definitions 1 and 2 and Section 7 Problem 58, use finite simple undirected graphs of order at least two. Global domination means domination in the graph and its loopless complement on the same vertices. SimpleGraph.IsDominating is the existing domination predicate: every vertex belongs to the set or has a neighbour in it. The complement has an edge precisely between distinct vertices that are not adjacent in the original graph.

The model definitions allow an arbitrary universe u and V : Type u; the braces on V indicate an implicit parameter. The closed question uses V : Type and W : Type, with Finite instances and Nat.card, so every actual finite vertex type in that universe is allowed. Only the counterexample is specifically labelled, by Fin 2. A and B in the graph formula are subtype vertices, and val extracts their actual subsets. No independent-block or maximum-partition condition is imposed.

**Definition 1.1 (Global domination).**

$$\forall \{V : Type_{u}\}, \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (A : \operatorname{Set}\left(V\right)), (\operatorname{GloballyDominating}\left(G, A\right)) \Leftrightarrow ((\operatorname{IsDominating}\left(G, A\right)) \land (\operatorname{IsDominating}\left(G^{c}, A\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.GloballyDominating` (`✓ std3`).

*Citation.* Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh (2025). *Global coalitions in graphs*. URL: <https://arxiv.org/abs/2509.15386v4>.

*Commentary.*

For every graph G and actual subset A, both G.IsDominating A and G-complement.IsDominating A must hold. The identical set A and vertex type V are used in both clauses.

**Definition 1.2 (Actual global coalitions).**

$$\forall \{V : Type_{u}\}, \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (A : \operatorname{Set}\left(V\right)), \forall (B : \operatorname{Set}\left(V\right)), (\operatorname{GlobalCoalition}\left(G, A, B\right)) \Leftrightarrow ((\operatorname{Disjoint}\left(A, B\right)) \land ((\neg (\operatorname{GloballyDominating}\left(G, A\right))) \land ((\neg (\operatorname{GloballyDominating}\left(G, B\right))) \land (\operatorname{GloballyDominating}\left(G, (A \cup B)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.GlobalCoalition` (`✓ std3`).

*Citation.* Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh (2025). *Global coalitions in graphs*. URL: <https://arxiv.org/abs/2509.15386v4>.

*Commentary.*

The four requirements are disjointness, failure of global domination for A, failure for B, and global domination of A union B. Ordinary coalition partitions can admit singleton dominating classes; these are not exceptions to the global definition.

**Definition 1.3 (Global coalition partition records).**

$$\forall \{V : Type_{u}\}, \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{GCPartition}\left(G\right) := \operatorname{structure} (blocks : \operatorname{Set}\left(\operatorname{Set}\left(V\right)\right)) (isPartition : Setoid.\operatorname{IsPartition}\left(blocks\right)) (partners : \forall (A : \operatorname{Set}\left(V\right)), (A \in blocks) \Rightarrow (\exists (B : \operatorname{Set}\left(V\right)), (B \in blocks) \land ((B \ne A) \land (\operatorname{GlobalCoalition}\left(G, A, B\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.GCPartition` (`✓ std3`).

*Citation.* Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh (2025). *Global coalitions in graphs*. URL: <https://arxiv.org/abs/2509.15386v4>.

*Commentary.*

GCPartition G is a structure with exactly the displayed three fields. blocks is a set of actual subsets of V. Setoid.IsPartition blocks says that the empty set is absent and each vertex belongs to a unique member of blocks; hence its members are nonempty, pairwise disjoint and cover V. partners quantifies over every member A, supplies B in the identical blocks, requires B distinct from A, and requires the complete GlobalCoalition G A B predicate. Individual non-domination follows from that predicate.

**Definition 1.4 (The actual blocks).**

$$\forall \{V : Type_{u}\}, \forall \{G : \operatorname{SimpleGraph}\left(V\right)\}, \forall (pi : \operatorname{GCPartition}\left(G\right)), pi.\operatorname{blocks} : \operatorname{Set}\left(\operatorname{Set}\left(V\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.blocks` (`✓ std3`).

*Citation.* Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh (2025). *Global coalitions in graphs*. URL: <https://arxiv.org/abs/2509.15386v4>.

*Commentary.*

The blocks field has type Set (Set V). The vertex type and graph parameters are implicit, followed by the explicit record parameter; its elements are the actual subsets, rather than labels or an independently chosen adjacency relation.

**Theorem 1.5 (The partition field).**

$$\forall \{V : Type_{u}\}, \forall \{G : \operatorname{SimpleGraph}\left(V\right)\}, \forall (pi : \operatorname{GCPartition}\left(G\right)), pi.\operatorname{isPartition} : Setoid.\operatorname{IsPartition}\left(pi.\operatorname{blocks}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.isPartition` (`✓ std3`). ∎

*Citation.* Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh (2025). *Global coalitions in graphs*. URL: <https://arxiv.org/abs/2509.15386v4>.

*Commentary.*

For every pi : GCPartition G, the isPartition field proves Setoid.IsPartition pi.blocks. This retains all nonempty-block, disjointness and cover requirements of a vertex partition.

**Theorem 1.6 (The partner field).**

$$\forall \{V : Type_{u}\}, \forall \{G : \operatorname{SimpleGraph}\left(V\right)\}, \forall (pi : \operatorname{GCPartition}\left(G\right)), pi.\operatorname{partners} : \forall (A : \operatorname{Set}\left(V\right)), (A \in pi.\operatorname{blocks}) \Rightarrow (\exists (B : \operatorname{Set}\left(V\right)), (B \in pi.\operatorname{blocks}) \land ((B \ne A) \land (\operatorname{GlobalCoalition}\left(G, A, B\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.partners` (`✓ std3`). ∎

*Citation.* Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh (2025). *Global coalitions in graphs*. URL: <https://arxiv.org/abs/2509.15386v4>.

*Commentary.*

For every pi and every actual A in pi.blocks, this field supplies an actual B in pi.blocks with B unequal to A and GlobalCoalition G A B. It has no exceptional singleton case.

**Definition 1.7 (The native graph on partition blocks).**

$$\forall \{V : Type_{u}\}, \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (pi : \operatorname{GCPartition}\left(G\right)), \forall (A : \{C : \operatorname{Set}\left(V\right) \mid C \in pi.\operatorname{blocks}\}), \forall (B : \{C : \operatorname{Set}\left(V\right) \mid C \in pi.\operatorname{blocks}\}), (\operatorname{Adj}\left(\operatorname{globalCoalitionGraph}\left(G, pi\right), A, B\right)) \Leftrightarrow (\operatorname{GlobalCoalition}\left(G, A.\operatorname{val}, B.\operatorname{val}\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.globalCoalitionGraph` (`✓ std3`).

*Citation.* Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh (2025). *Global coalitions in graphs*. URL: <https://arxiv.org/abs/2509.15386v4>.

*Commentary.*

The result has type SimpleGraph {A : Set V // A belongs to pi.blocks}. Its adjacency is exactly the displayed full coalition predicate. Symmetry exchanges A and B, uses symmetric disjointness and commutativity of union. A loop would make A union A globally dominating while A is not; union self gives a contradiction. Thus the native symmetric, loopless graph uses the actual coalition relation.

**Definition 1.8 (The complete universal realizability question).**

$$(claim) \Leftrightarrow (\forall (V : Type), \forall [\operatorname{Finite}\left(V\right)], (2 \le Nat.\operatorname{card}\left(V\right)) \Rightarrow (\forall (H : \operatorname{SimpleGraph}\left(V\right)), \exists (W : Type), \exists (_ : \operatorname{Finite}\left(W\right)), \exists (G : \operatorname{SimpleGraph}\left(W\right)), (2 \le Nat.\operatorname{card}\left(W\right)) \land (\exists (pi : \operatorname{GCPartition}\left(G\right)), \operatorname{Nonempty}\left((SimpleGraph.\operatorname{Iso}\left(\operatorname{globalCoalitionGraph}\left(G, pi\right), H\right))\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.claim` (`✓ std3`).

*Citation.* Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh (2025). *Global coalitions in graphs*. URL: <https://arxiv.org/abs/2509.15386v4>.

*Commentary.*

Problem 58 asks: Is every graph realisable as a global coalition graph? In full, for every finite actual target type V of order at least two and every simple graph H on V, there exist an arbitrary finite actual host type W of order at least two, a simple graph G on W, an actual global coalition partition pi of G, and an ordinary graph isomorphism from its global coalition graph to H. Finite V is an anonymous instance binder. The existential Finite W proof is anonymous; G, its order bound and pi all belong to that same W. The earlier v1 Section 6 Problem 4 asks the same realizability question without the order restrictions; it is a separate statement boundary for the same question.

**Theorem 1.9 (Negation of the whole universal assertion).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh (2025). *Global coalitions in graphs*. URL: <https://arxiv.org/abs/2509.15386v4>.

*Commentary.*

The theorem states not claim, with every target, host and partition quantifier as above. Use the edgeless graph on Fin 2, which has order two. For any proposed host G and any actual pi, an isomorphism to this target has a preimage A of vertex zero. The partners field supplies B in the same partition and an actual global coalition between A and B, hence an actual adjacent pair in globalCoalitionGraph G pi. The isomorphism transports this adjacency to the edgeless target, a contradiction. The private lemma no_edgeless_realization supplies this argument for arbitrary universe-polymorphic hosts and arbitrary nonempty edgeless targets, and result applies it to Fin 2. This excludes every host and eligible partition for one legal target, rather than only a selected host. The same argument also excludes that target under the unrestricted v1 question. Whether every isolate-free target is globally realizable remains unsettled here; no classification or realization construction follows. No conclusion about the paper's other results or literature priority is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.GCPartition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.GlobalCoalition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.GloballyDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.blocks`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.globalCoalitionGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.isPartition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.partners`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination](../../../ConceptDynamics/GraphColoring/GraphCoverDomination.md)
