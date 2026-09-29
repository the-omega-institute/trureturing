# Face signatures around global edges

## Abstract

Directed face-signature transitions balance on every global edge.

Number each tetrahedron's edges (12,13,14,34,24,23). Pairing corresponding edge slots across faces generates the equivalence classes of actual global edges. Every tetrahedron contributes six distinct local edge occurrences, even when several belong to the same global edge. A color is assigned to each global edge, and every face has one or two low edges.

A fixed-point-free involution pairs whole faces, and the three edge slots on each face are transported by an inverse pair of permutations. This pairing admits a compatible orientation of every normal edge link. Each outgoing face is mapped to the next incoming face. Its single three-edge permutation sends the outgoing local edge slot to the next local edge occurrence. The resulting successor permutes all occurrences along oriented normal edge links and preserves their global-edge classes.

The Boolean signature records a face count of one as false and two as true. A rise is a one-to-two transition; a fall is a two-to-one transition. A path end is a local edge at an end of the three-edge path formed by edges of its own color.

**Theorem 1.1 (Rises equal falls and path ends have even multiplicity).**

$$\forall T \in Type, finite \in Fintype\left(T\right), p \in RawFacePairing\left(T\right), c \in GlobalEdge\left(p\right) \to Bool, v \in ValidColoring\left(p, c\right), e \in GlobalEdge\left(p\right),\; rise\left(p, c, v, e\right) = fall\left(p, c, v, e\right) \land Even\left(pathEndCount\left(p, c, v, e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/EdgeStarTransitions.global_edge_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each actual global edge of a finite face-paired tetrahedron system, the number of one-to-two transitions equals the number of two-to-one transitions. Local path-end edge occurrences on that same global edge have even multiplicity.

A six-edge incidence check identifies a local path end exactly when its two adjacent face signatures differ. Gluing preserves all three labels on a paired face, so each outgoing signature equals the next incoming one. Reindexing by the label-preserving successor makes the transition counts equal; their sum is therefore even.

The conclusion concerns colored face incidence on the normal circle and uses no edge lengths or angle estimates.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/EdgeStarTransitions.global_edge_balance`
- Dependency: [D5/S3/Geometry/Hyperideal/FaceSignaturePropagation](FaceSignaturePropagation.md)
