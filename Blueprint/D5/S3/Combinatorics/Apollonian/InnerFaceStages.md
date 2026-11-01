# Inner-face Apollonian stages

## Abstract

The deterministic finite inner-face Apollonian stages and their source-derived combinatorial laws.

**Definition 1.1 (Inner faces).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Face`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Face` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural stage n, Face 0 is Fin 3 and Face (n+1) is Face n × Fin 3. The child label records the omitted old corner. This index contains only the inner faces; it does not contain the outer triangle.

**Definition 1.2 (Persistent vertices).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Vertex`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

Vertex 0 is Fin 4. Vertex (n+1) is the disjoint sum Vertex n ⊕ Face n. An inl vertex is retained, and inr f is the one distinct vertex inserted into inner face f.

**Definition 1.3 (Ordered corners).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.corner`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.corner` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

Seed vertices 0,1,2,3 are a,b,c,o. Face f at stage zero has corners (3,f,f+1 modulo 3), with the outer indices included in Fin 4. For child (f,i), corner i is inr f and every other corner j is inl (corner n f j). Thus exactly one centre and two retained corners bound each child triangle.

**Definition 1.4 (Corner incidence).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Incident`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Incident` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

Incident n f v means there exists an index i in Fin 3 with corner n f i = v. It refers to the actual ordered triangle of f.

**Definition 1.5 (Exact adjacency recursion).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.adjacent`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

At stage zero, two seed vertices are adjacent exactly when distinct. At a successor stage, old-old adjacency is exactly previous adjacency; old-new adjacency means that the old endpoint is a corner of the new endpoint’s parent face. New-new adjacency is false. The relation is symmetric and irreflexive.

**Definition 1.6 (The finite simple stage graph).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.graph`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.graph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural n, graph n is the simple unweighted graph on Vertex n with the recursively constructed adjacency. Both the vertex and inner-face types carry finite enumerations and decidable equality. Every subdivision is simultaneous over all indexed inner faces.

**Definition 1.7 (Incident inner-face count).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.faceCount`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.faceCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For n and v in Vertex n, faceCount n v is the sum over f in Face n of one when Incident n f v holds and zero otherwise. It counts only current inner faces.

**Definition 1.8 (Pair incidence count).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.pairFaceCount`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.pairFaceCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For n and u,v in Vertex n, pairFaceCount n u v counts current inner faces containing both u and v. It is not the number of all graph common neighbours.

**Definition 1.9 (Adjacency row count).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For n and v in Vertex n, degreeCount n v is the sum over all u in Vertex n of the zero-one indicator of actual adjacency from v to u.

**Theorem 1.10 (Incident faces of a retained vertex).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.faceCount_old`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.faceCount_old` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural n and v in Vertex n, faceCount (n+1) (inl v) = 2*faceCount n v. Each incident parent face gives exactly two incident children.

**Theorem 1.11 (Incident faces at insertion).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.faceCount_new`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.faceCount_new` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural n and current inner face f, the vertex inr f at stage n+1 belongs to exactly three inner child faces.

**Theorem 1.12 (Distinct persistent seed vertices).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural n the map seed n from Fin 4 to Vertex n is injective.

**Theorem 1.13 (Degree increment of a retained vertex).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_old`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_old` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural n and v in Vertex n, degreeCount (n+1) (inl v) = degreeCount n v + faceCount n v. The retained vertex acquires exactly one neighbour from each currently incident inner face.

**Theorem 1.14 (Inner-face indices do not duplicate triangles).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.inner_faces_distinct`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.inner_faces_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every n and f,g in Face n, if Incident n f v is equivalent to Incident n g v for every v in Vertex n, then f=g. At a successor stage the unique new corner determines the parent; injectivity of the parent corner triple then determines the omitted corner.

**Definition 1.15 (Canonical stage inclusion).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.embed`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.embed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For n,t natural and v in Vertex n, embed n 0 v is v and embed n (t+1) v is inl (embed n t v), lying in Vertex (n+t+1). Thus the same persistent vertex is identified at all later stages.

**Definition 1.16 (Actual insertion stage).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.birth`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.birth` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

The four seed vertices have birth zero. A retained vertex keeps its birth, and inr f at stage n+1 has birth n+1. Every vertex at stage n has birth at most n.

**Theorem 1.17 (Adjacency persists exactly).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.adjacent_embed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.adjacent_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For all natural n,t and u,v in Vertex n, adjacency of embed n t u and embed n t v in stage n+t is equivalent to adjacency of u and v in stage n. There are no later edges between two old vertices.

**Theorem 1.18 (The cutoff partition is the actual birth partition).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.old_vertices_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.old_vertices_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For all natural k,t and w in Vertex (k+t), birth (k+t) w ≤ k if and only if there exists u in Vertex k with embed k t u = w. The canonical inclusion is injective, so old vertices have unique representatives.

**Theorem 1.19 (Exact degree of every inserted vertex).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every n, v in Vertex n, and positive birth j=birth n v, degreeCount n v = 3·2^(n−j). The new vertex starts with three neighbours and three inner incident faces; each subsequent subdivision doubles its incident-face count and adds that many neighbours. Natural subtraction is used, with j≤n proved from the constructor.

**Theorem 1.20 (Uniform degree bound after a cutoff).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_late_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_late_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For all natural n,k and v in Vertex n satisfying k < birth n v, degreeCount n v ≤ 3·2^(n−k−1). This is derived from the exact birth-degree law and monotonicity of the natural power, without a degree assumption.

**Definition 1.21 (The labelled seed vertices).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every n, seed n includes Fin 4 in Vertex n by iterating inl. Indices 0,1,2 give the distinguished outer triangle, and index 3 is the original centre.

**Theorem 1.22 (Exact seed degrees at every stage).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural n and v in Fin 4, degreeCount n (seed n v) is 3·2^n when v=3 and 2^(n+1)+1 otherwise. These are precisely the centre and the three outer vertices. The arbitrary-stage induction includes the initial face and degree computations and sums the constructor’s incident-face increments; the source’s displayed degrees are not premises.

**Theorem 1.23 (The count is the ordinary graph degree).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_eq_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_eq_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every n and v in Vertex n, degreeCount n v equals (graph n).degree v. Thus all the stated degree counts refer to the same simple graph used for ordinary adjacency.

**Theorem 1.24 (A second eigenvalue index is available).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.card_vertex_ge_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.card_vertex_ge_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural n, 4 ≤ Fintype.card (Vertex n). The four seed vertices remain distinct. No closed formula for the total number of vertices is needed or asserted.

**Definition 1.25 (Actual late common neighbours).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.lateCommonCount`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.lateCommonCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For k,t natural and u,v in Vertex k, lateCommonCount k t u v counts w in Vertex (k+t) satisfying k < birth (k+t) w and adjacency to both embed k t u and embed k t v. It counts vertices of the actual graph, including the diagonal case u=v.

**Definition 1.26 (Orientation by birth).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Oriented`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Oriented` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

Oriented n u v means actual adjacency together with birth n v < birth n u. The directed edge runs from the newer endpoint to the older endpoint.

**Theorem 1.27 (At most three older neighbours).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.oriented_outdegree_le_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.oriented_outdegree_le_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every n and u in Vertex n, the number of v with Oriented n u v is at most three. Seed-to-seed edges have equal birth and receive no birth orientation. Inserted vertices have exactly their three parent corners as older neighbours; later subdivisions preserve those edges and add only younger neighbours.

**Theorem 1.28 (Every edge of the late induced graph is oriented).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.late_edge_oriented`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.late_edge_oriented` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For all natural n,k and u,v in Vertex n with both births greater than k and with u adjacent to v, Oriented n u v or Oriented n v u holds. Distinct inserted vertices in one generation are never adjacent. Hence an edge of the late induced graph has unequal endpoint births.

**Theorem 1.29 (Indegree bound in the late graph).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.late_oriented_indegree_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.late_oriented_indegree_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For n,k and u in Vertex n with birth greater than k, the number of v with birth greater than k and Oriented n v u is at most 3·2^(n−k−1). The count is bounded by the actual graph degree and then by the proved birth-degree estimate.

**Definition 1.30 (Ordinary adjacency over the reals).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.adjacency`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.adjacency` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

adjacency n is exactly (graph n).adjMatrix over the real numbers. Its entries are one at edges and zero elsewhere; there is no weighting, normalization, Laplacian substitution or randomness.

**Definition 1.31 (The actual later vertex type).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.LateVertex`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.LateVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

LateVertex k t is the subtype of Vertex (k+t) consisting of vertices w with k < birth (k+t) w. The complementary old subtype is identified with Vertex k by the proved canonical-inclusion characterization.

**Definition 1.32 (The exact old and late partition).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoffEquiv`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoffEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every fixed cutoff k and natural t, cutoffEquiv identifies Vertex k ⊕ LateVertex k t with Vertex (k+t). Its old branch is embed k t and its late branch is subtype inclusion. Injectivity uses preserved births; surjectivity uses the old-vertex characterization. Every actual graph vertex occurs exactly once.

**Definition 1.33 (The old-to-late adjacency block).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoffBlock`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoffBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For k,t natural, cutoffBlock k t is the rectangular real matrix with rows u in Vertex k and columns w in LateVertex k t. Its entry is adjacency (k+t) (embed k t u) w.val. The two index sets can have different cardinalities.

**Definition 1.34 (The actual late induced adjacency).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.lateAdjacency`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.lateAdjacency` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

lateAdjacency k t restricts the ordinary real adjacency of stage k+t to LateVertex k t in both coordinates. It is the remainder block C in the fixed-cutoff proof.

**Theorem 1.35 (Exact adjacency block decomposition).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For all k,t and all vertices u,v of Vertex k ⊕ LateVertex k t, adjacency (k+t) evaluated at cutoffEquiv u and cutoffEquiv v equals the corresponding entry of the block matrix [[adjacency k, cutoffBlock k t], [transpose (cutoffBlock k t), lateAdjacency k t]]. Old-old equality is exact edge persistence, mixed equality is the definition of the incidence block and symmetry, and late-late equality is restriction. This is an exact change of vertex coordinates, with no spectral estimate assumed.

**Theorem 1.36 (Exact Gram diagonal).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_gram_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_gram_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For all k,t natural and u in Vertex k, the u,u entry of cutoffBlock k t times its transpose is the real cast of (graph (k+t)).degree (embed k t u) − (graph k).degree u, with subtraction in Nat. The decomposition of degree into old and late neighbours proves that this subtraction is the intended nonnegative degree increment.

**Theorem 1.37 (Common-neighbour estimate for the actual Gram matrix).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_gram_offdiag`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_gram_offdiag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For all k,t natural and distinct u,v in Vertex k, the u,v entry of B Bᵀ, where B=cutoffBlock k t, is nonnegative and at most 2t over the reals. If u,v are not adjacent at stage k, this entry is zero. Each new common neighbour is the centre of a face containing both old vertices; there are at most two such current inner faces, and no later old-old edge appears.

**Definition 1.38 (The second spectral index).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.secondIndex`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.secondIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural n, secondIndex n is index one in Fin (card (Vertex n)). The proved lower bound four supplies its strict bound. Indices are zero based.

**Definition 1.39 (The ordinary ordered second eigenvalue).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.secondEigenvalue`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.secondEigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural n, secondEigenvalue n is Mathlib’s decreasing real Hermitian eigenvalues₀ list for (graph n).adjMatrix over the reals, evaluated at secondIndex n. The imported ordered-spectrum API counts eigenvalues with their characteristic-polynomial multiplicities. It uses the actual simple graph and ordinary adjacency.

**Definition 1.40 (The exact spectral target).**

Lean statement: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.limitClaim`

*Formalization.* `D5/S3/Combinatorics/Apollonian/InnerFaceStages.limitClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

limitClaim is Tendsto, along all natural n tending to infinity, of secondEigenvalue n divided by the real power 2^((n:Real)/2), to sqrt(2). The real exponent preserves odd stages. This declaration defines the original target; SecondEigenvalueLimit.result proves it from the actual graph and its cutoff spectral estimates.

## References

- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Face`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Incident`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.LateVertex`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Oriented`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.adjacency`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.adjacent`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.adjacent_embed`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.birth`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.card_vertex_ge_four`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.corner`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoffBlock`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoffEquiv`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_adjacency`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_gram_diag`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.cutoff_gram_offdiag`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_eq_degree`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_inner`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_late_le`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.degreeCount_old`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.embed`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.faceCount`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.faceCount_new`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.faceCount_old`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.graph`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.inner_faces_distinct`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.lateAdjacency`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.lateCommonCount`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.late_edge_oriented`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.late_oriented_indegree_le`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.limitClaim`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.old_vertices_iff`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.oriented_outdegree_le_three`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.pairFaceCount`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.secondEigenvalue`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.secondIndex`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed_degrees`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/InnerFaceStages.seed_injective`
