# Opposite-parity cross faces

## Abstract

Counting opposite cross faces at a fixed axis

**Theorem 1.1 (At most 28 distinct geometric faces).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CrossWitnessTotal.cross_opposite_faces_union_card_le_28`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CrossWitnessTotal.cross_opposite_faces_union_card_le_28` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a main axis in the nine-cube. The two supports are disjoint and nonadjacent, induce cubic subgraphs and are Huang-balanced. A geometric four-face is specified by its active directions and frozen bits. In each direction, we may count any finite family of faces with an opposite projected-parity witness across the two supports. Each face may use any ordering of its anchor star and either endpoint as root.

Separation forces a selected apex with all three transverse neighbours in paired fibres. The main-axis mate of the apex is absent by cubicity. Its projection therefore identifies the selected apex, whose directions and frozen bits recover the face. For each witness parity this injects the faces into the single fibres with three paired neighbours.

The Huang energy estimate bounds three times the number of these faces by twice the number of paired fibres of the witness parity. The two witness-parity classes cover each family. Pooling the bounds in both directions and using one main-axis edge per six vertices gives nine times the size of the geometric union at most the total support size. At total size at most 258, the union has at most 28 faces.

**Theorem 1.2 (At most 17 distinct geometric faces of a common witness parity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CrossWitnessTotal.arbitrary_matched_parity_cross_faces_union_card_le_17`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CrossWitnessTotal.arbitrary_matched_parity_cross_faces_union_card_le_17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every face in both families admits a witness of the same projected parity, each witness uses a paired anchor fibre of the complementary parity. The union of directions at the two endpoints of that edge determines the five-face. The apex projection complements its four transverse bits and preserves the other projected bits, so the anchor fibre determines the projection for every ordering and either choice of root.

The unique selected apex over that projection determines the geometric face. Thus in each direction the faces inject into actual complementary anchor fibres. Combining these injections with the energy bound on the witness parity gives fifteen times the size of the geometric union at most the total support size. At total size at most 258, the union has at most 17 faces.

These bounds constrain candidate supports for Hong, Wu and Xia's Problem 2. The 258-point case remains open. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CrossWitnessTotal.arbitrary_matched_parity_cross_faces_union_card_le_17`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CrossWitnessTotal.cross_opposite_faces_union_card_le_28`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EdgeStarAmbient](Q9EdgeStarAmbient.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairedFibreAnyAxis](Q9PairedFibreAnyAxis.md)
