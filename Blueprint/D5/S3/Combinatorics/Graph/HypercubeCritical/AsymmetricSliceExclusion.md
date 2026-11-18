# The asymmetric parameter branch has no induced realization in a finite cube

## Abstract

Exclusion of the asymmetric induced-cube slice with parameters (13,11;7,1).

Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f₂(Q₉) is 3 or 4. The published problem and its preceding reductions and results are due to that paper. The original 258-point construction and the obligation to exclude the full remaining alternative remain unresolved. This document proves the exclusion of one specific asymmetric local parameter branch, including extraction from every slice satisfying its stated parameters. Novelty of this local branch is unconfirmed. Other 48-vertex parameter cases remain open; this result does not settle Problem 2 or exclude all 48-vertex candidates.

**Definition 1.1 (The closed asymmetric slice proposition).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal closed proposition claim asserts that there exist n : ℕ, S : Finset (Fin n → Bool), and L,R : Finset {x : Fin n → Bool // x ∈ S}, such that, writing G = (hypercube n).induce {x | x ∈ S}, G.IsBipartiteWith L R holds on the subtype of vertices in S; every vertex x satisfies G.degree x = 2 or G.degree x = 3; no adjacent vertices both have degree 2; (8 : ℕ∞) ≤ G.egirth; L.card = 13 and R.card = 11; and (degreeTwo G L).card = 7 and (degreeTwo G R).card = 1.

Here degreeTwo G L and degreeTwo G R select the degree-2 vertices on the two sides. Adjacency in G is exactly cube adjacency restricted to the finite subset S. Positive degree makes L and R cover S, and their disjoint side counts force S to have 24 vertices; this cardinality is derived, not an extra hypothesis or a chosen reindexing. Dimension is unrestricted, including n = 0. There is no additional saturation, high-label table, seven-pair, embedding, or external certificate hypothesis. This public definition is the proposition refuted by the public theorem result.

**Theorem 1.2 (Exclusion by extraction of the forbidden induced slice).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem result has exactly type ¬ claim. Call degree-3 vertices high and degree-2 vertices low. The parameters give six high vertices in L and ten in R. The equality 15·6 = 6·11 + 2·10 + 4·1 forces equality in the one-step and three-step nonbacktracking endpoint bound from GirthSliceCounting. Girth at least eight gives uniqueness of these endpoints and disjointness of the length-1 and length-3 endpoint images. Hence each high left root reaches every vertex of R by an edge or a nonbacktracking path of length three. At a right high vertex let g count high neighbors and j count low neighbors. Local equality and j + g = 3 give j·g = 2, so g is 1 or 2. Six right high vertices have g = 2 and four have g = 1; the sole right low vertex z has two high neighbors. Individual left-root path counts force each of the six high left vertices to meet exactly two g = 2 connectors.

Compress each actual g = 2 connector to an edge between its two high left neighbors. Girth makes the connector unique for its endpoints and forbids compressed triangles, producing a 2-regular graph on six vertices. The two high neighbors u,v of z are nonadjacent in this core and have no common core neighbor. Consequently the core is the six-cycle with edges u-x1, u-x2, v-y1, v-y2, x1-y1, x2-y2, whose respective connector labels are a,b,c,d,e,f. Degree three supplies four further right high vertices X1,X2,Y1,Y2, with singleton high neighborhoods x1,x2,y1,y2 respectively. The eleven labels z,a,b,c,d,e,f,X1,X2,Y1,Y2 are distinct and exhaust R. All labels and incidence tables are extracted from the actual graph.

Two right labels form a low pair when they share an actual degree-2 vertex. Common high neighbors and genuine four-edge paths through high left vertices, together with girth at least eight, exclude all pairs outside fifteen unordered possibilities: a-d, a-Y2, b-c, b-Y1, c-X2, d-X1, e-f, e-X2, e-Y2, f-X1, f-Y1, X1-X2, X1-Y2, X2-Y1, Y1-Y2. The closed finite witness check ranges over Fin 11 right labels and Fin 6 high left labels; it supplies the required short-path obstructions without assuming an exhaustive graph classification. Saturated endpoint coverage then forces the four actual low pairs a-Y2, b-Y1, c-X2, d-X1.

Independently, every right high vertex has degree three and at most two high neighbors, so it has an actual low neighbor. That low vertex has a second, distinct endpoint in R, yielding an actual low-pair partner. For X1,X2,Y1,Y2 the high-neighbor count is one, so each has two distinct low neighbors. Girth forbids these two low neighbors from sharing their other endpoint. Thus two distinct partners are proved to exist. Combining these facts with the four forced pairs and the short-path exclusions forces e-f, X1-X2, Y1-Y2. The seven pairs are exactly a-Y2, b-Y1, c-X2, d-X1, e-f, X1-X2, Y1-Y2, each with an actual degree-2 witness.

Choose one witness for each of these seven pairs. Each witness has degree two, so its two distinct endpoints exhaust its neighborhood. Distinct endpoint pairs therefore give seven distinct low vertices. Their degrees distinguish them from the six high left vertices, and the bipartition distinguishes all thirteen left vertices from the eleven right vertices. The resulting label map F : Fin 24 → actual vertices is injective. Closed finite checks establish endpoint-pair identification, injectivity of the label tags, edge types, and the explicit neighbor counts. Every edge of the explicit 32-edge graph is an actual graph edge under F.

At each label, the actual degree equals the neighbor cardinality in the explicit graph. Injectivity and edge preservation thus saturate every actual neighbor set, proving adjacency reflection as well. Hence F is an induced embedding. Composing F with the injective subtype inclusion x ↦ x.val gives an induced embedding of the explicit graph into the finite cube of dimension n, contradicting the proved AsymmetricSliceNonEmbedding.result, whose argument uses coordinate flips and parity. Extraction, the seven actual pairs, the finite checks, and the induced embedding all participate in this proof of ¬ claim; no extra embedding or seven-pair assumptions enter the theorem.

The trust boundary is ordinary Lean/Mathlib proof checking. Closed finite index and table obligations use decide +kernel and finite case splits with ordinary kernel proof terms; generic counting and graph arguments are symbolic. The imported nonembedding result is reused as a proved dependency. Classical choices of labels and witnesses stay within the standard axiom boundary, including Classical.choice and standard propositional and quotient logic. No problem-specific extra axiom, sorry, external SAT or oracle trust, or native_decide is introduced by this host. The bounded computation concerns finite label obligations, not enumeration of arbitrary cube dimensions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding](AsymmetricSliceNonEmbedding.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSlicePairs](AsymmetricSlicePairs.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting](GirthSliceCounting.md)
