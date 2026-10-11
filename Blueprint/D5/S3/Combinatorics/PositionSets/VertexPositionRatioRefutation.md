# The vertex position ratio is unbounded

## Abstract

A connected graph family has quadratically many vertices on a sphere from one vertex, but only linearly many geodesic rays from another. Its vertex position ratio is unbounded.

**Definition 1.1 (Membership in a shortest path).**

$$\forall (V:\operatorname{Type}), \forall (G:\operatorname{SimpleGraph}(V)), \forall (x:V), \forall (y:V), \forall (z:V), (\operatorname{OnGeodesic}(G, x, y, z)) \iff (\exists (p:G.\operatorname{Walk}(x, y)), (p.\operatorname{length} = G.\operatorname{dist}(x, y)) \land (z \in p.\operatorname{support}))$$

*Formalization.* `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.OnGeodesic` (`✓ std3`).

*Citation.* M. Thankachy, E. J. Thomas, U. Chandran, J. Tuite, G. Di Stefano, G. Erskine (2024). *On the Vertex Position Number of Graphs*. DOI: [10.7151/dmgt.2491](https://doi.org/10.7151/dmgt.2491). URL: <https://arxiv.org/abs/2209.00359v2>.

*Commentary.*

Definition 2.1, page 3 of arXiv:2209.00359v2, uses the phrase "lies on any x,y-geodesic in G". OnGeodesic G x y z means that z belongs to the support of a walk from x to y whose length equals the graph distance. Such a walk is a shortest path; its support includes both endpoints. The predicate expresses existence of one such path.

**Definition 1.2 (Position relative to a vertex).**

$$\forall (V:\operatorname{Type}), \forall (G:\operatorname{SimpleGraph}(V)), \forall (x:V), \forall (S:\operatorname{Finset}(V)), (\operatorname{IsXPositionSet}(G, x, S)) \iff (\forall (y:V), (y \in S) \longrightarrow (\forall (z:V), (z \in S) \longrightarrow ((z \ne y) \longrightarrow (\neg (\operatorname{OnGeodesic}(G, x, y, z))))))$$

*Formalization.* `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.IsXPositionSet` (`✓ std3`).

*Citation.* M. Thankachy, E. J. Thomas, U. Chandran, J. Tuite, G. Di Stefano, G. Erskine (2024). *On the Vertex Position Number of Graphs*. DOI: [10.7151/dmgt.2491](https://doi.org/10.7151/dmgt.2491). URL: <https://arxiv.org/abs/2209.00359v2>.

*Commentary.*

Definition 2.1, page 3: "For any graph G and a fixed vertex x ∈ V(G), a set Sₓ ⊆ V(G) is an x-position set if for any y ∈ Sₓ no vertex of Sₓ \ {y} lies on any x,y-geodesic in G." The finite set S represents Sₓ. For each selected y, every other selected z is excluded from every shortest x,y-path. This includes the endpoint x: a set containing x and another vertex fails the condition in a connected graph. The singleton {x} is permitted.

**Definition 1.3 (The x-position number).**

$$\forall (V:\operatorname{Type}), [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] \forall (G:\operatorname{SimpleGraph}(V)), \forall (x:V), \operatorname{posNum}(G, x) = ((\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}(\operatorname{Finset}(V))).\operatorname{filter}(\operatorname{IsXPositionSet}(G, x))).\operatorname{sup}(\operatorname{Finset}.\operatorname{card})$$

*Formalization.* `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.posNum` (`✓ std3`).

*Citation.* M. Thankachy, E. J. Thomas, U. Chandran, J. Tuite, G. Di Stefano, G. Erskine (2024). *On the Vertex Position Number of Graphs*. DOI: [10.7151/dmgt.2491](https://doi.org/10.7151/dmgt.2491). URL: <https://arxiv.org/abs/2209.00359v2>.

*Commentary.*

Definition 2.1, page 3: "The x-position number of G is defined to be the maximum cardinality of an x-position set and is denoted by pₓ(G) or simply pₓ." The finite supremum ranges over all finite subsets of V satisfying IsXPositionSet G x, including the empty set. Finset.card counts vertices once; the full finite carrier, not a chosen candidate list, is used.

**Definition 1.4 (The upper vertex position number).**

$$\forall (V:\operatorname{Type}), [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] \forall (G:\operatorname{SimpleGraph}(V)), \operatorname{vp}(G) = (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}(V)).\operatorname{sup}(\operatorname{posNum}(G))$$

*Formalization.* `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.vp` (`✓ std3`).

*Citation.* M. Thankachy, E. J. Thomas, U. Chandran, J. Tuite, G. Di Stefano, G. Erskine (2024). *On the Vertex Position Number of Graphs*. DOI: [10.7151/dmgt.2491](https://doi.org/10.7151/dmgt.2491). URL: <https://arxiv.org/abs/2209.00359v2>.

*Commentary.*

Definition 2.1, page 3: "The maximum value of pₓ(G) among all vertices x of G is called the upper vertex position number vp(G) (or simply the vertex position number) of G." vp takes the supremum of posNum over the entire finite vertex carrier.

**Definition 1.5 (The minimum vertex position number).**

$$\forall (V:\operatorname{Type}), [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] [\operatorname{Nonempty}(V)] \forall (G:\operatorname{SimpleGraph}(V)), \operatorname{vpMinus}(G) = (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}(V)).\operatorname{inf}'(\operatorname{posNum}(G))$$

*Formalization.* `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.vpMinus` (`✓ std3`).

*Citation.* M. Thankachy, E. J. Thomas, U. Chandran, J. Tuite, G. Di Stefano, G. Erskine (2024). *On the Vertex Position Number of Graphs*. DOI: [10.7151/dmgt.2491](https://doi.org/10.7151/dmgt.2491). URL: <https://arxiv.org/abs/2209.00359v2>.

*Commentary.*

Definition 2.1, pages 3–4: "Similarly, the minimum value of pₓ(G) among all vertices of G is called the minimum vertex position number vp⁻(G) of G." Nonempty V ensures that Finset.univ is nonempty. The proof argument of inf' is suppressed in the formula; it is Finset's proof that the universal finite set is nonempty. Every vertex is included.

**Definition 1.6 (Problem 2.4: boundedness on connected graphs).**

$$(\operatorname{claim}) \iff (\exists (C:\mathbb R), \forall (V:\operatorname{Type}), [\operatorname{Fintype}(V)] [\operatorname{DecidableEq}(V)] [\operatorname{Nonempty}(V)] \forall (G:\operatorname{SimpleGraph}(V)), [\operatorname{DecidableRel}(G.\operatorname{Adj})] (G.\operatorname{Connected}) \longrightarrow ((\operatorname{vp}(G):\mathbb R) \le C \cdot (\operatorname{vpMinus}(G):\mathbb R)))$$

*Formalization.* `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.claim` (`✓ std3`).

*Citation.* M. Thankachy, E. J. Thomas, U. Chandran, J. Tuite, G. Di Stefano, G. Erskine (2024). *On the Vertex Position Number of Graphs*. DOI: [10.7151/dmgt.2491](https://doi.org/10.7151/dmgt.2491). URL: <https://arxiv.org/abs/2209.00359v2>.

*Commentary.*

Problem 2.4, page 5: "Is the ratio vp(G)/vp⁻(G) bounded for connected graphs?" The question is encoded as one real constant C valid for every finite nonempty vertex carrier and every connected simple graph on it, with decidable adjacency. The numbers are coerced from naturals to reals. A singleton is an x-position set, so vpMinus is positive on these carriers; multiplication by it faithfully expresses ratio boundedness. No bound on graph order or restriction to a subclass is imposed.

**Theorem 1.7 (A family refutes the proposed boundedness).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/thankachy-et-al-2024-vertex-position-ratio` (refuted) by `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"thankachy-et-al-2024-vertex-position-ratio","declaration_gid":"D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Thankachy, E. J. Thomas, U. Chandran, J. Tuite, G. Di Stefano, G. Erskine (2024). *On the Vertex Position Number of Graphs*. DOI: [10.7151/dmgt.2491](https://doi.org/10.7151/dmgt.2491). URL: <https://arxiv.org/abs/2209.00359v2>.

*Commentary.*

For each integer m ≥ 2, take one hub y and 2m+1 paths meeting only at y: H of length 4m, m paths Pᵢ of length 4m, and m paths Qⱼ of length aⱼ = 2m+2j for 1 ≤ j ≤ m. Add H at level bⱼ to Qⱼ at the same level, where bⱼ = 2m+j+1; join the tip Qⱼ at level aⱼ to every Pᵢ at that level. An edge changes its level by at most one, so every ray is shortest from y. A y-position set meets each ray in at most one vertex, giving posNum at y at most 2m+1. At x = H at level 4m, a second potential changes by at most one along every edge. Together with explicit walks, it puts all m(m−1) vertices Pᵢ at levels aⱼ+1, for j < m, at distance 2m+1 from x. A sphere is an x-position set: any different selected vertex inside a shortest path would have smaller distance from x. Consequently vp is at least m(m−1) and vpMinus is at most 2m+1. The quadratic lower bound exceeds C(2m+1) for some m for each real C. This contradicts claim. The lower bound, rather than an exact value of either invariant on the family, suffices. The source's separate degree, eccentricity and graph-class results are not assertions of boundedness and retain their stated scopes.

## References

- Truth anchor: `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.IsXPositionSet`
- Truth anchor: `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.OnGeodesic`
- Truth anchor: `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.posNum`
- Truth anchor: `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.vp`
- Truth anchor: `D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.vpMinus`
