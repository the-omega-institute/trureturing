# Finite graph invariants

## Abstract

Finite graph independence and upper star formation

These definitions and local characterizations apply to arbitrary finite simple graphs. A star is a subgraph and need not be induced. Inclusion-minimality is distinct from minimum cardinality. The two-independent neighbor characterization also applies to every finite simple graph.

**Definition 1.1 (Selected induced degree is less than k).**

$$\operatorname{IsKIndependent}\left(G, k, I\right) \Leftrightarrow \left(\forall v \in V,\; \operatorname{Member}\left(v, I\right) \Rightarrow \operatorname{d}\left(G, I, v\right) < k\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.IsKIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each selected vertex has fewer than k selected neighbours. For k equal to two, the induced graph is a disjoint union of edges and isolated vertices.

**Definition 1.2 (Maximum k-independent cardinality).**

$$\operatorname{beta}\left(G, k\right) = \operatorname{supCard}\left(\{I \in \operatorname{powerset}\left(\operatorname{univ}\left(V\right)\right) \mid \operatorname{IsKIndependent}\left(G, k, I\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the maximum cardinality over the k-independent subsets of V. The finite supremum has value zero if the family is empty.

**Definition 1.3 (A star containing each outside vertex).**

$$\operatorname{IsStarForming}\left(G, k, S\right) \Leftrightarrow \left(\forall v \in V,\; \left(\neg \operatorname{Member}\left(v, S\right)\right) \Rightarrow \left(\exists c \in V,\; \exists L \in \operatorname{Finset}\left(V\right),\; \operatorname{card}\left(L\right) = k \land \left(\left(\neg \operatorname{Member}\left(c, L\right)\right) \land \left(\operatorname{Subset}\left(\operatorname{insert}\left(c, L\right), \operatorname{insert}\left(v, S\right)\right) \land \left(\left(\forall ell \in V,\; \operatorname{Member}\left(ell, L\right) \Rightarrow \operatorname{Adj}\left(G, c, ell\right)\right) \land \operatorname{Member}\left(v, \operatorname{insert}\left(c, L\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.IsStarForming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every vertex outside S, the graph on S together with that vertex contains a star with k leaves containing the vertex. The centre is distinct from all leaves. Extra edges between leaves are allowed: the star is a subgraph, with no induced-subgraph requirement.

**Definition 1.4 (Inclusion-minimal star formation).**

$$\operatorname{IsMinimalStarForming}\left(G, k, S\right) \Leftrightarrow \left(\operatorname{IsStarForming}\left(G, k, S\right) \land \left(\forall T \in \operatorname{Finset}\left(V\right),\; \operatorname{ProperSubset}\left(T, S\right) \Rightarrow \left(\neg \operatorname{IsStarForming}\left(G, k, T\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.IsMinimalStarForming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set is star-forming and no proper subset is star-forming. This is inclusion-minimality rather than minimum cardinality.

**Definition 1.5 (Upper k-star-forming number).**

$$\operatorname{SF}\left(G, k\right) = \operatorname{supCard}\left(\{S \in \operatorname{powerset}\left(\operatorname{univ}\left(V\right)\right) \mid \operatorname{IsMinimalStarForming}\left(G, k, S\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.SF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the maximum cardinality among all inclusion-minimal k-star-forming sets. The finite supremum has value zero if the family is empty.

**Definition 1.6 (Two local alternatives).**

$$\operatorname{LocalTwo}\left(G, S\right) \Leftrightarrow \left(\forall v \in V,\; \left(\neg \operatorname{Member}\left(v, S\right)\right) \Rightarrow \left(2 \le \operatorname{d}\left(G, S, v\right) \lor \left(\exists u \in V,\; \operatorname{Member}\left(u, S\right) \land \left(\operatorname{Adj}\left(G, v, u\right) \land 1 \le \operatorname{d}\left(G, S, u\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.LocalTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every outside vertex either has two neighbours in S, or has a neighbour in S that itself has a neighbour in S. In the second alternative this further neighbour cannot be the outside vertex.

**Theorem 1.7 (The local criterion equals the star definition).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Finset}\left(V\right),\; \operatorname{IsStarForming}\left(G, 2, S\right) \Leftrightarrow \operatorname{LocalTwo}\left(G, S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.starForming_two_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a two-leaf star, the outside vertex is either the centre, giving two neighbours in S, or a leaf, giving a centre and another leaf in S. Conversely, two selected neighbours give a star centred at the outside vertex; a selected neighbour with its own selected neighbour gives a star centred at that selected neighbour. The argument works on any vertex type with decidable equality and adjacency.

**Theorem 1.8 (The exact selected-neighbor condition).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.independent_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.independent_iff` (`✓ std3`). ∎

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

For every finite simple graph with decidable equality and adjacency, a finite set is two-independent exactly when any two selected neighbors of a selected vertex are equal. This is the original local grafting proof's characterization, also used by canonical composition and cover arguments. No grafting or nonempty hypothesis is needed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.IsKIndependent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.IsMinimalStarForming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.IsStarForming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.LocalTwo`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.SF`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.independent_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants.starForming_two_iff`
