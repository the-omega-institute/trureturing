# Density from Pairs and Triangles

## Abstract

Hereditary cut bounds charge three distinct representatives more strongly than two, through a multigraph of parallel edges and triangles.

Let V be a finite vertex set and E a finite set of indexed edges, with two distinct endpoints l(e) and r(e) for every edge. Parallel edges retain their different indices. TwoCutCap means that for every S contained in V and every L contained in S, the number of edges with one endpoint in L and the other in S minus L is at most 2|S|. The bound is required on every induced vertex set, not only on cuts of V.

**Theorem 1.1 (A Multigraph Bound with Cut Capacity Two).**

$$\forall V \in \mathrm{Finset}\left(Vertex\right),\; \forall E \in \mathrm{Finset}\left(Edge\right),\; \forall l \in \mathrm{Function}\left(Edge, Vertex\right),\; \forall r \in \mathrm{Function}\left(Edge, Vertex\right),\; (\mathrm{DistinctEndpoints}\left(E, l, r\right) \land \left(\mathrm{EndpointsIn}\left(V, E, l, r\right) \land \mathrm{TwoCutCap}\left(V, E, l, r\right)\right)) \Rightarrow (2 \cdot \mathrm{card}\left(E\right) \le 7 \cdot \mathrm{card}\left(V\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HyperedgeCutDensity.two_cut_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every endpoint lies in V and TwoCutCap holds, then 2|E| is at most 7|V|. Averaging cuts gives fewer than 4|S| internal edges on every nonempty S. The degree sum therefore yields a vertex of degree at most seven. Deleting and restoring such vertices constructs an eight-coloring. Regard its colors as three-bit vectors and take the seven cuts given by nonzero binary linear forms. Each edge crosses exactly four cuts, while each cut contains at most 2|V| edges. Summing gives 4|E| at most 14|V|.

For the owner bound, let I be a finite set of indexed owners, let large assign a Boolean flag to each owner, and choose representatives a(i), b(i), c(i) in V. Always require a(i) different from b(i). A flagged owner must have all three representatives distinct. For an unflagged owner, c(i) need not be distinct and may equal a(i). Let T be the flagged owners. A representative set hits a cut when its intersection with S meets both L and S minus L. The hereditary owner condition bounds the number of hitting owners by |S| for every S contained in V and every L contained in S. Owners count once, regardless of how many of their representatives cross the cut.

**Theorem 1.2 (The Additional Cost of a Third Representative).**

$$\forall V \in \mathrm{Finset}\left(Vertex\right),\; \forall I \in \mathrm{Finset}\left(Owner\right),\; \forall large \in \mathrm{Function}\left(Owner, Bool\right),\; \forall a \in \mathrm{Function}\left(Owner, Vertex\right),\; \forall b \in \mathrm{Function}\left(Owner, Vertex\right),\; \forall c \in \mathrm{Function}\left(Owner, Vertex\right),\; (\mathrm{DistinctPairs}\left(I, a, b\right) \land \left(\mathrm{DistinctThirdWhenFlagged}\left(I, large, a, b, c\right) \land \left(\mathrm{RepresentativesIn}\left(V, I, a, b, c\right) \land \mathrm{HereditaryOwnerCutBound}\left(V, I, a, b, c\right)\right)\right)) \Rightarrow (4 \cdot \mathrm{card}\left(I\right) + 2 \cdot \mathrm{card}\left(\mathrm{FlaggedOwners}\left(I, large\right)\right) \le 7 \cdot \mathrm{card}\left(V\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HyperedgeCutDensity.mixed_owner_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated distinctness, containment and hereditary owner conditions, 4|I| plus 2|T| is at most 7|V|. Give each unflagged owner two indexed parallel edges joining a(i) and b(i), and each flagged owner the triangle on its three representatives. An owner contributes at most two crossing edges to any induced cut, and contributes none unless its representative set hits the cut. The resulting graph therefore satisfies TwoCutCap and has exactly 2|I|+|T| edges. Apply the preceding graph bound. Empty owner and vertex sets are included. If representatives are selected from larger supports, the owner condition follows from the corresponding cut bound on those supports; this requires containment of each representative in its own support.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HyperedgeCutDensity.mixed_owner_density`
- Truth anchor: `D5/S3/Combinatorics/Graph/HyperedgeCutDensity.two_cut_density`
- Dependency: [D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity](BipartiteSubgraphDensity.md)
