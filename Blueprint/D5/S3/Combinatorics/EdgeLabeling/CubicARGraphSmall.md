# The small cubic graphs

## Abstract

Degree and cardinality determine the small cubic graph forms.

**Theorem 1.1 (Six vertices of degree two).**

$$\operatorname{card}\left(V\right) = 6 \land \forall v, \operatorname{degree}\left(H, v\right) = 2 \implies \operatorname{TwoTrianglesOrSixCycle}\left(H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall.two_regular_six_presentation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every simple graph on six vertices in which every vertex has degree two has a listing of six distinct vertices covering the vertex set. Its neighbor sets in that listing are either those of two disjoint triangles or those of a six-cycle. A triangle exhausts the two neighbors of each of its vertices, and forces the remaining three vertices to form a triangle. Without a triangle, two extensions from the neighbors of one vertex must be distinct. Closing them early would leave at most two vertices of degree two, which is impossible. They therefore close through the unique remaining vertex to give a six-cycle.

**Theorem 1.2 (A listing as an equivalence).**

$$\operatorname{PairwiseDistinct}\left(a, b, c, d, e, f\right) \land V = \operatorname{ListingSet}\left(a, b, c, d, e, f\right) \implies \exists q: \operatorname{Equiv}\left(\operatorname{Fin}\left(6\right), V\right), \operatorname{MatchesListing}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall.six_listing_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any pairwise distinct listing a,b,c,d,e,f covering a finite vertex type gives an equivalence q from Fin 6 to that type, with q(0)=a, q(1)=b, q(2)=c, q(3)=d, q(4)=e, and q(5)=f.

**Theorem 1.3 (Four-vertex cubic graphs).**

$$\operatorname{card}\left(V\right) = 4 \land \forall v, \operatorname{degree}\left(G, v\right) = 3 \implies \forall x, y, \operatorname{Adj}\left(G, x, y\right) \iff x \neq y$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall.cubic_four_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a simple cubic graph with four vertices, adjacency is precisely inequality. Each neighbor set has three elements and is contained in the other three vertices, so equality follows by cardinality.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall.cubic_four_complete`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall.six_listing_equiv`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall.two_regular_six_presentation`
