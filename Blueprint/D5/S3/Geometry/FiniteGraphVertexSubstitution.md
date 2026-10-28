# Single-vertex graph substitution

## Abstract

The actual singleton-fiber substitution decomposition in finite coordinates.

**Theorem 1.1 (Recovery of embedded coordinates).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.mapped_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphVertexSubstitution.mapped_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For all finite source and target vertex types U and X, every pre-abstract complex K on U, every vertex embedding f from U to X, and every point y in the coordinate realization of K mapped by f, the function sending z to the sum over u of y(f(u)) when f(u)=z, and zero otherwise, equals y. A mapped face contains no ambient vertex outside the embedding image, so all such coordinates vanish. Injectivity reduces every image coordinate to its unique source coordinate.

**Definition 1.2 (Native realization transport along an embedding).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.mapHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.mapHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For all finite vertex types U and X, every pre-abstract complex K on U, and every embedding f from U to X, the native finite-coordinate realization of K is homeomorphic to that of K mapped by f. The forward map sums coordinates over the preimage of each vertex; the inverse restricts the coordinates at f(u). Nonnegativity, the coordinate sum one, and support in a mapped face prove membership. Both maps are continuous finite-coordinate maps. Unused ambient vertices are allowed.

**Definition 1.3 (The actual independence complex).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.independenceComplex`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.independenceComplex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every simple graph, the faces are exactly its nonempty finite independent vertex sets. Every singleton is present, as required by Mathlib's abstract simplicial complex convention. An unoccupied fiber contributes an empty selected set, rather than a required nonempty face.

**Definition 1.4 (Heterogeneous graph substitution).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.substitution`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.substitution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For a base graph G and a graph H(u) on each current fiber D(u), the vertices are the dependent pairs (u,d). Adjacency holds over a base edge, or within one fiber according to H(u). Fibers may be empty.

**Definition 1.5 (The current vertices away from v).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.Tail`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.Tail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The tail is the dependent sum of D(u) over all base vertices unequal to v. It keeps every current fiber without changing its graph.

**Definition 1.6 (The restricted base for the link).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.LinkBaseSet`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.LinkBaseSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The link base consists of all u unequal to v for which G has no edge from v to u. This is the complement of the closed neighborhood in the current base graph.

**Definition 1.7 (The current-fiber link vertices).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.LinkVerts`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.LinkVerts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The link vertices are the dependent sum of the original current fibers D(u) over the restricted link base. Any earlier fiber replacements remain present on this restriction.

**Definition 1.8 (The restricted substitution independence complex).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.linkComplex`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.linkComplex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Restrict G to the link base, retain H(u) on D(u), form their heterogeneous substitution, and take its actual independence complex. The resulting pre-abstract complex may have no faces.

**Definition 1.9 (The replacement sigma family).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.newFiber`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.newFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For a distinguished base vertex v and a finite new vertex type W, the new family has W at v and the old D(u) at every other u. The construction includes the dependent casts between these branch types.

**Definition 1.10 (Finiteness of the replacement fibers).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.newFiberFintype`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.newFiberFintype` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The replacement fibers are finite because W and every current D(u) are finite.

**Definition 1.11 (Decidable equality on replacement fibers).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.newFiberDecidableEq`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.newFiberDecidableEq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Decidable equality on W and each D(u) supplies decidable equality on each branch of the replacement family.

**Definition 1.12 (The actual graphs on the replacement family).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.newGraphs`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.newGraphs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Use the new graph on W at v and H(u) at every other vertex, transported across the defining branch equalities of the new family.

**Definition 1.13 (The old distinguished coordinate point).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.oldPoint`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.oldPoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every current substitution and chosen d0 in D(v), the old point is the coordinate singleton (v,d0) in its independence realization.

**Definition 1.14 (The pure-right singleton).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.joinPoint`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.joinPoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every l0 in W, the point of the simplicial join is its pure-right coordinate singleton l0. It exists even if the restricted link complex has no faces. No ordinary topological join or point of the link realization is used.

**Definition 1.15 (The actual quotient-wedge decomposition).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.oneVertexReplacementEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.oneVertexReplacementEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Let V and all current fibers D(u) be finite, let G be a simple base graph and H(u) a simple graph on D(u), choose v and d0 in D(v), and suppose every d in D(v) equals d0. For every finite graph Hnew on W and l0 in W, the coordinate independence realization of the actual new sigma substitution is homotopy equivalent to the actual quotient wedge of the old independence realization at (v,d0) and the realization of the simplicial join of the current restricted link complex with the independence complex of Hnew, based at the pure-right singleton l0. No other fiber or link nonemptiness is assumed. On the common carrier Tail plus W, A is embedded deletion union the join with the pre-complex whose sole face is the singleton l0; B is the embedded full simplicial join, and their exact intersection is that singleton-apex cone. The cone remains nonempty when the link has no faces. The cone-union equivalence is followed by an actual quotient homeomorphism induced by two apex-preserving homeomorphisms of the summands. The singleton old-fiber hypothesis rules out a residual old fiber at v. This all-finite-case coordinate decomposition is a local realization refinement for the lexicographic-product setting of Carnero Bravo arXiv:2505.06457v2, not a theorem attributed to that paper. Theorem 21 there concerns suspended independence complexes; Question 22 asks for unsuspended hereditary membership in the class W. The present bridge asserts neither that question's resolution nor a novelty claim. An ordinary-join interpretation requires both factor realizations to be nonempty and is outside this statement.

**Definition 1.16 (Graph isomorphism transport).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.graphIsoHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.graphIsoHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every isomorphism of finite simple graphs, transport the actual independence realization by the vertex equivalence. The exact equality of mapped independent faces reuses the original restricted-map proof; the coordinate embedding homeomorphism then gives the actual homeomorphism, including empty graphs.

**Definition 1.17 (Fiberwise substitution transport).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.substitutionFiberIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.substitutionFiberIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For a fixed base graph and a graph isomorphism on every fiber, the dependent-sum equivalence preserves and reflects substitution adjacency and keeps the base coordinate. This is consumed in the actual mixed-stage identifications.

**Definition 1.18 (Nested induced graph reindexing).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.nestedInduceIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.nestedInduceIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For a subset B of the base and a subset S of B, send a nested subtype vertex to its underlying base vertex in the image of S under subtype projection. This explicit bijection identifies the twice-induced graph with the original graph induced on that image, and transports the hereditary base hypothesis in the smaller-link induction.

**Definition 1.19 (Singleton fibers recover the base).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.singletonSubstitutionIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.singletonSubstitutionIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Substitution of an edge-free singleton at every base vertex is isomorphic to the base graph by projection, with inverse adjoining the unique singleton element. Empty and singleton base graphs are included.

**Definition 1.20 (The augmented empty-left simplicial unit).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.emptyLeftJoinHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.emptyLeftJoinHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

If M has no faces, every surviving face of its simplicial join with N is purely right. Thus the join is exactly N mapped by the right vertex embedding, and their actual realizations are homeomorphic. No identification with the ordinary join of an empty space is asserted.

**Definition 1.21 (The actual mixed replacement family).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiber`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

At a vertex in the replaced finset use its final fiber D(v); elsewhere use PUnit in the same fiber universe. This family retains all previously replaced fibers on every restricted current link.

**Definition 1.22 (Finiteness of the mixed fibers).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiberFintype`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiberFintype` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Each mixed fiber is finite by its selected finite final-fiber or singleton branch.

**Definition 1.23 (Decidable equality of the mixed fibers).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiberDecidableEq`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiberDecidableEq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Branch reduction transfers decidable equality from each final fiber or from the singleton.

**Definition 1.24 (Nonempty mixed fibers).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiberNonempty`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiberNonempty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

If every final fiber is nonempty, both branches of every mixed fiber are nonempty. This supplies actual current-link vertices when the restricted base is nonempty.

**Definition 1.25 (Graphs on the mixed family).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageGraphs`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageGraphs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Transport H(v) across the selected branch equality, and transport the edge-free singleton graph across the other branch equality. These are graphs on the actual dependent stage types.

**Definition 1.26 (The initial stage is the base graph).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.initialStageIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.initialStageIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The stage with no replaced vertices is isomorphic to the base graph, by fiberwise singleton transport and projection. This starts replacement induction without an order-two assumption.

**Definition 1.27 (The final stage is full substitution).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.finalStageIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.finalStageIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The stage indexed by the full base finset is isomorphic to the full original heterogeneous substitution, by the explicit selected-fiber equivalences.

**Definition 1.28 (A supplier replacement is the next mixed stage).**

Lean statement: `D5/S3/Geometry/FiniteGraphVertexSubstitution.replacementStageIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphVertexSubstitution.replacementStageIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Pointwise branch casts identify the supplier newFiber construction at v with the stage indexed by insert v R, preserving actual fiber adjacency. When v is absent from R, the old stage fiber at v is a singleton; no singleton assumption is made on the new final fiber. These transports serve the private strong induction on base cardinality and inner induction on replaced vertices. Its homotopy-class inputs are explicit point, nonempty ordinary-join, coordinate-vertex quotient-wedge and homotopy-invariance closure assumptions, not discharged properties of the source class W. The link carries all current mixed fibers. A nonempty link uses the smaller-base induction, and an empty link uses the augmented simplicial unit. Full Question 22 still requires the actual accepted topology closures and both source-model normalization directions.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.LinkBaseSet`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.LinkVerts`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.Tail`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.emptyLeftJoinHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.finalStageIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.graphIsoHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.independenceComplex`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.initialStageIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.joinPoint`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.linkComplex`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.mapHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.mapped_coordinates`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.nestedInduceIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.newFiber`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.newFiberDecidableEq`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.newFiberFintype`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.newGraphs`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.oldPoint`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.oneVertexReplacementEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.replacementStageIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.singletonSubstitutionIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiber`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiberDecidableEq`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiberFintype`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageFiberNonempty`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.stageGraphs`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.substitution`
- Truth anchor: `D5/S3/Geometry/FiniteGraphVertexSubstitution.substitutionFiberIso`
- Dependency: [D5/S3/Geometry/FiniteConeUnionWedge](FiniteConeUnionWedge.md)
- Dependency: [D5/S3/Geometry/FiniteSimplicialJoin](FiniteSimplicialJoin.md)
