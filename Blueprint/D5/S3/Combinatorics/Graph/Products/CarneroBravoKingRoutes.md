# The 178-route induced king-grid certificate

## Abstract

The actual prescribed subdivision and its induced finite king-grid embedding for the Question 32 route.

Carnero Bravo, arXiv:2505.06457v2 Question 32, asks whether the hereditary sphere-wedge statement for king grids of widths at most four extends to every width. An induced subgraph is the relevant target. Question 35 instead concerns the full grid. This module implements the embedding interface of the proposed Question 32 counterexample; it does not prove a homology obstruction or settle either question.

The original labels, edges, coordinates and 178 corner lists are literal scientific inputs. The seed belongs to Adamaszek's Small flag complexes with torsion, arXiv:1208.3892v1; the graph-move route follows the Barmak/Lozin approach. The explicit coordinate construction and its formal certificate are local. No independent original-problem or unique credit is claimed.

**Definition 1.1 (The actual prescribed subdivision).**

$$\mathrm{subdivision}:\operatorname{Data}\left(\mathrm{Original}, \mathrm{Edge}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.subdivision` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Original is the subtype of the 141 retained natural labels, Edge is Fin 178, and the exact 178 route records specify the endpoints and k(e). Fresh vertices are tagged by their edge and an index in Fin (3 k(e)). The coordinate of an interior vertex is sample(corners(e),i+1), with every corner and detour retained.

**Theorem 1.2 (The complete finite route facts).**

$$\forall e \in \mathrm{Edge},\; \left(\neg \operatorname{corners}\left(\operatorname{route}\left(e\right)\right) = \mathrm{Nil}\right) \land \left(\operatorname{axisAligned}\left(\operatorname{corners}\left(\operatorname{route}\left(e\right)\right)\right) \land \left(\operatorname{length}\left(\operatorname{corners}\left(\operatorname{route}\left(e\right)\right)\right) = 3 \cdot \operatorname{k}\left(\mathrm{subdivision}, e\right) + 1 \land \left(\operatorname{sample}\left(\operatorname{corners}\left(\operatorname{route}\left(e\right)\right), 0\right) = \operatorname{oldCoordinate}\left(\operatorname{left}\left(\mathrm{subdivision}, e\right)\right) \land \operatorname{sample}\left(\operatorname{corners}\left(\operatorname{route}\left(e\right)\right), 3 \cdot \operatorname{k}\left(\mathrm{subdivision}, e\right) + 1\right) = \operatorname{oldCoordinate}\left(\operatorname{right}\left(\mathrm{subdivision}, e\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.polyline_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every actual route, the corner list is nonempty and axis-aligned, its Manhattan length is 3 k(e)+1, and its samples at positions zero and 3 k(e)+1 equal the old endpoint coordinates. This is a kernel-reduction obligation over the literal data.

**Theorem 1.3 (Every path position has the verifier's coordinate).**

$$\forall e \in \mathrm{Edge},\; \forall i \in \operatorname{Fin}\left(3 \cdot \operatorname{k}\left(\mathrm{subdivision}, e\right) + 1 + 1\right),\; \operatorname{coordinate}\left(\operatorname{pathVertex}\left(\mathrm{subdivision}, e, i\right)\right) = \operatorname{getElem}\left(\operatorname{verifierExpand}\left(\operatorname{corners}\left(\operatorname{route}\left(e\right)\right)\right), \operatorname{val}\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.path_coordinate_verifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every e and every position i in Fin (3 k(e)+2), coordinate(pathVertex(e,i)) is exactly element i of verifierExpand(corners(e)). The index is proved to lie within the expanded route, so this statement uses actual element access. Old coordinates likewise use a proved-present table entry. No Python output is a proof premise.

**Theorem 1.4 (Every original edge is represented).**

$$\operatorname{image}\left(\mathrm{fun} (e:\mathrm{Edge}) \mapsto \operatorname{SymPair}\left(\operatorname{left}\left(\operatorname{route}\left(e\right)\right), \operatorname{right}\left(\operatorname{route}\left(e\right)\right)\right), \operatorname{univ}\left(\mathrm{Edge}\right)\right) = \mathrm{constructionEdges}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.endpoint_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The image of all route indices under the unordered endpoint-pair function equals the literal 178-edge construction inventory.

**Theorem 1.5 (Distinct route indices have distinct endpoint pairs).**

$$\operatorname{Injective}\left(\mathrm{fun} (e:\mathrm{Edge}) \mapsto \operatorname{SymPair}\left(\operatorname{left}\left(\operatorname{route}\left(e\right)\right), \operatorname{right}\left(\operatorname{route}\left(e\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.endpoint_pair_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The endpoint-pair map from Edge to unordered pairs of original natural labels is injective. Together with the exact inventory this identifies the routes with the edges of the actual original simple graph.

**Theorem 1.6 (Exact old-graph incidence).**

$$\forall a \in \mathrm{Original},\; \forall b \in \mathrm{Original},\; \operatorname{Adj}\left(\mathrm{baseGraph}, a, b\right) \Leftrightarrow \left(\exists e \in \mathrm{Edge},\; \left(a = \operatorname{left}\left(\mathrm{subdivision}, e\right) \land b = \operatorname{right}\left(\mathrm{subdivision}, e\right)\right) \lor \left(a = \operatorname{right}\left(\mathrm{subdivision}, e\right) \land b = \operatorname{left}\left(\mathrm{subdivision}, e\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.baseGraph_iff_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For all a,b in Original, baseGraph.Adj(a,b) iff some route has endpoints (a,b) in one of the two orders. No replacement graph or assumed graph isomorphism occurs in this interface.

**Theorem 1.7 (Every occupancy value is the actual successful fill).**

$$\forall b \in \mathrm{Nat},\; \operatorname{ListMem}\left(b, \mathrm{routingBuckets}\right) \Rightarrow \operatorname{bucketFill}\left(\mathrm{routingBucket}, \operatorname{rawVertices}\left(\mathrm{subdivision}, \mathrm{originalVertices}, \mathrm{edgeIndices}\right), \mathrm{rawCoordinate}, b\right) = \operatorname{some}\left(\operatorname{apply}\left(\mathrm{actualTrees}, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.actual_tree_fills` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For each of the sixteen buckets, bucketFill of the original tag list is some(actualTrees(b)). Lean's evaluator generates and quotes untrusted tree values. Each exact fill equation is proved separately by kernel reduction against the original enumeration, so correctness does not depend on the evaluator. The tree values have no runtime implementation. Subsequent kernel checks use their definitions, and local soundness consumes the proved fill equations.

**Theorem 1.8 (The actual occupancy check).**

$$\operatorname{routingCheck}\left(\mathrm{routingBucket}, \mathrm{routingBuckets}, \operatorname{rawVertices}\left(\mathrm{subdivision}, \mathrm{originalVertices}, \mathrm{edgeIndices}\right), \operatorname{rawEdgePairs}\left(\mathrm{subdivision}, \mathrm{edgeIndices}\right), \mathrm{rawCoordinate}, \operatorname{rawGraph}\left(\mathrm{subdivision}\right), \mathrm{actualTrees}\right) = \mathrm{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.routing_check_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

routingCheck on the natural tags of the actual old and fresh vertices equals true. An interior tag is its actual edge number and natural position; rawCoordinate uses the same corner sampler. The tag map is proved injective, its enumerated list is proved complete, and its edge inventory and graph adjacency are proved equivalent to those of RoutedGraph. Sixteen coordinate buckets are checked in blocks of at most 64 entries. The evaluator supplies only candidate lists: the kernel proves their equality with the original enumeration, checks each block, and combines the results with List.all_append. Neighbor queries select their own coordinate bucket, so cross-boundary adjacencies are included. Together with actual_tree_fills, these checks prove freshness and both adjacency implications through routingCheck_sound. Four spatial queries per occupied point suffice; no enumeration of every pair of the 93,999 vertices occurs.

**Theorem 1.9 (Injection and both adjacency implications).**

$$\operatorname{Injective}\left(\mathrm{coordinate}\right) \land \left(\forall v \in \mathrm{Vertex},\; \forall w \in \mathrm{Vertex},\; \operatorname{Adj}\left(\mathrm{RoutedGraph}, v, w\right) \Leftrightarrow \operatorname{squareAdj}\left(\operatorname{coordinate}\left(v\right), \operatorname{coordinate}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.exact_square_routing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

coordinate is injective and, for every pair of actual vertices, RoutedGraph adjacency is equivalent to Manhattan distance one between their coordinates. This is the soundness application consumed by the finite embedding.

**Theorem 1.10 (The inclusive bounds of the literal transform).**

$$\forall v \in \mathrm{Vertex},\; 1 \le \operatorname{fst}\left(\operatorname{rotate}\left(\operatorname{coordinate}\left(v\right)\right)\right) \land \left(\operatorname{fst}\left(\operatorname{rotate}\left(\operatorname{coordinate}\left(v\right)\right)\right) \le 9337 \land \left(1 \le \operatorname{snd}\left(\operatorname{rotate}\left(\operatorname{coordinate}\left(v\right)\right)\right) \land \operatorname{snd}\left(\operatorname{rotate}\left(\operatorname{coordinate}\left(v\right)\right)\right) \le 9061\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.actual_T_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every actual vertex v, T(coordinate(v))=(x+y+25,x-y+1705) lies in [1,9337] times [1,9061]. Both coordinates are one-based and both are reduced by one when entering the Fin types.

**Definition 1.11 (The actual finite induced embedding).**

$$\mathrm{inducedEmbedding}:\operatorname{GraphEmbedding}\left(\mathrm{RoutedGraph}, \operatorname{strongProduct}\left(\operatorname{pathGraph}\left(9337\right), \operatorname{pathGraph}\left(9061\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.inducedEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

inducedEmbedding maps RoutedGraph into the strong product of pathGraph 9337 and pathGraph 9061 on Fin 9337 times Fin 9061. Its coordinate map is (T_x-1,T_y-1). The strong product includes Mathlib boxProd edges and simultaneous factor adjacency, so it is the finite king grid. The map is injective and reflects as well as preserves every adjacency.

**Definition 1.12 (Isomorphism onto the induced range).**

$$\mathrm{inducedIso}:\operatorname{GraphIso}\left(\mathrm{RoutedGraph}, \operatorname{induce}\left(\mathrm{rectangle}, \mathrm{selected}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.inducedIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

selected is the actual set-theoretic range of inducedEmbedding. The pinned Mathlib isoInduceRange construction yields RoutedGraph isomorphic to rectangle.induce(selected). Thus the target is an induced subgraph of the stated finite rectangle.

**Theorem 1.13 (The exact prescribed multiplicity sum).**

$$\sum_{e \in \mathrm{Edge}} \operatorname{k}\left(\mathrm{subdivision}, e\right) = 31286$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.sum_subdivisions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The sum over the 178 actual k(e) is 31286. This is the number of triple subdivisions needed to form the prescribed paths after the separate graph-move stage.

**Theorem 1.14 (Exactly 93,999 vertices).**

$$\operatorname{FintypeCard}\left(\mathrm{Vertex}\right) = 93999$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.actual_vertex_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

RoutedGraph has 141 old vertices and 93858 fresh vertices, hence 93999 vertices. This follows from the general tagged-subdivision cardinality formula and the exact multiplicity data.

**Theorem 1.15 (Exactly 94,036 edges).**

$$\operatorname{card}\left(\operatorname{edgeFinset}\left(\mathrm{RoutedGraph}\right)\right) = 94036$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.actual_edge_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The exact routed graph has 94036 edges, the sum of 3 k(e)+1 over all 178 routes. No quadratic vertex-pair enumeration is required for this count.

**Theorem 1.16 (The induced range has 93,999 vertices).**

$$\operatorname{FintypeCard}\left(\mathrm{selected}\right) = 93999$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.selected_vertex_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The range isomorphism transfers the exact vertex cardinality to selected.

**Theorem 1.17 (The induced range has 94,036 edges).**

$$\operatorname{card}\left(\operatorname{edgeFinset}\left(\operatorname{induce}\left(\mathrm{rectangle}, \mathrm{selected}\right)\right)\right) = 94036$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.selected_edge_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The range isomorphism transfers the exact edge cardinality to rectangle.induce(selected).

The routing module leaves separate homological obligations: replay of the supplied 40 graph moves from the Adamaszek seed with the actual ambient edges, identification of prescribed subdivisions with genuine suspension moves, transport of the torsion class through those moves, and application of the finite-chain/singular-homology comparison and sphere-wedge torsion obstruction. KingFinalComposition discharges these obligations. The large routing certificate supplies none of those homology conclusions as an assumption.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.actual_T_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.actual_edge_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.actual_tree_fills`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.actual_vertex_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.baseGraph_iff_endpoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.endpoint_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.endpoint_pair_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.exact_square_routing`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.inducedEmbedding`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.inducedIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.path_coordinate_verifier`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.polyline_facts`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.routing_check_success`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.selected_edge_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.selected_vertex_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.subdivision`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.sum_subdivisions`
- Dependency: [D5/S3/Combinatorics/Graph/Products/IntegerPolyline](IntegerPolyline.md)
- Dependency: [D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision](PrescribedSubdivision.md)
