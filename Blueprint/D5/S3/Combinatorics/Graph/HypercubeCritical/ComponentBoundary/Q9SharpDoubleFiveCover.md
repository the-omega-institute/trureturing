# Fourteen triples on eight points and singleton masks on nine axes

## Abstract

The sharp eight-point double-cover bound and its Q9 application

**Theorem 1.1 (Double coverage on eight points requires fourteen triples).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover.fourteen_le_card_of_double_five_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover.fourteen_le_card_of_double_five_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every five-set of an eight-point set contains at least two triples from a family of distinct triples, the family has at least fourteen members.

The thirteen-triple lower bound reduces the proof to excluding equality at thirteen. Deletion counting and the Fano link bound cap every point degree at five. The degree sum then forces one point of degree four and seven of degree five. On those seven points, the pairs of codegree one form a triangle-free graph with at least eleven edges. Its parts have sizes four and three. Internal pairs require codegree at least two and crossing pairs require at least one. The codegree sum exceeds this baseline by one, so at most one pair exceeds its baseline. Each mixed triple on the seven points must contain that pair, which bounds the number of such triples by three. They can account for at most six crossing pairs, and the four triples through the degree-four point for at most four more. All twelve crossing pairs must occur.

**Theorem 1.2 (A cyclic family attains the bound).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover.exists_fourteen_triple_double_five_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover.exists_fourteen_triple_double_five_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the residues modulo seven, take the seven translates of {0, 1, 3}. Add the triples formed by adjoining the eighth point to each consecutive pair in the seven-cycle. Lean checks that the fourteen triples cover each of the 56 five-sets at least twice.

**Theorem 1.3 (At most twenty direction types force a singleton five-axis mask).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover.exists_singleton_five_mask_of_card_le_twenty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover.exists_singleton_five_mask_of_card_le_twenty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A family of at most twenty distinct triples on nine axes that covers every five-axis mask has a mask containing exactly one triple. If every mask were doubly covered, the nine eight-axis deletions would require at least 126 incidences. Each triple survives six deletions, for at most 120 incidences.

In a subcubic 258-vertex induced subgraph of Q9, take an actual component with universal Huang saturation. Use the distinct full direction sets at its degree-three vertices as the triple family. Singularity at every five-axis mask gives coverage by those triples. With at most twenty distinct types, the singleton mask gives a common full direction triple for every degree-three vertex whose directions lie in that mask. If the component is balanced, the same mask is singular and the masked-face theorem yields an eleven-vertex masked component with the three four-edge paths of its normal form. This is a conditional restriction for Hong, Wu and Xia's open Problem 2, which asks whether f₂(Q₉) is three or four. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover.exists_fourteen_triple_double_five_cover`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover.exists_singleton_five_mask_of_card_le_twenty`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover.fourteen_le_card_of_double_five_cover`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FanoDeletion](Q9FanoDeletion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SevenVertexBipartite](Q9SevenVertexBipartite.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask](Q9SingletonFiveMask.md)
- Narrative reference: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation](Q9ComponentSaturation.md)
- Narrative reference: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage](Q9DirectionCoverage.md)
- Narrative reference: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedFiveFace](Q9MaskedFiveFace.md)
