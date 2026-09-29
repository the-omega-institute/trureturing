# Critical edge face-signature words

## Abstract

A critical six-occurrence edge star has at most one two-count face signature.

A raw face pairing defines actual global edges from paired face-edge slots. Let s be its oriented edge-star structure after a valid low/high coloring. An element i of the fiber over a global edge has a local occurrence occ(i) and a six-edge position slot(i). The signature of occ(i) records whether its incoming face has two low edges.

**Theorem 1.1 (At most one two-count face).**

$$\forall T \in Type, finite \in Fintype\left(T\right), p \in RawFacePairing\left(T\right), c \in GlobalEdge\left(p\right) \to Bool, v \in ValidColoring\left(p, c\right), e \in GlobalEdge\left(p\right),\; \left(color\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), e\right) = true \land \left(\left(\forall i \in Fiber\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), e\right),\; 3 \le highNeighbourCount\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), occ\left(i\right)\right), slot\left(i\right)\right)\right) \land \left(edgeDegree\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), e\right) = 6 \land 4 \le fourHighCount\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), e\right)\right)\right)\right) \Rightarrow \left(\left(\forall i \in Fiber\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), e\right),\; \left(highNeighbourCount\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), occ\left(i\right)\right), slot\left(i\right)\right) = 4 \land colorCard\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), occ\left(i\right)\right), slot\left(i\right)\right) = 2\right) \lor \left(highNeighbourCount\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), occ\left(i\right)\right), slot\left(i\right)\right) = 3 \land isPathEnd\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), occ\left(i\right)\right), slot\left(i\right)\right)\right)\right) \land \left(\left(pathEndCount\left(p, c, v, e\right) = 0 \lor pathEndCount\left(p, c, v, e\right) = 2\right) \land \left(\left(\forall i \in Fiber\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), e\right),\; \neg {signature\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), occ\left(i\right)\right) = true \land signature\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), next\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), occ\left(i\right)\right)\right) = true}\right) \land twoFaceCount\left(edgeStars\left(toFacePairedTriangulation\left(p, c, v\right)\right), e\right) \le 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/CriticalEdgeSignatureWord.critical_edge_signature_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a low global edge has six local occurrences. Each has at least three high neighbours, and at least four have four high neighbours. Every occurrence is then either a two-low-edge local pair with four high neighbours or a three-high-neighbour path end. The number of path ends is zero or two.

No occurrence has both its incoming and successor face signatures equal to two. Around the actual global-edge circle, the resulting binary word forbids adjacent ones and contains at most one one.

The claim reads face incidence only. It does not identify the opposite edge as another critical global edge, assign shared lengths, or construct a hyperbolic geometry.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/CriticalEdgeSignatureWord.critical_edge_signature_word`
- Dependency: [D5/S3/Geometry/Hyperideal/EdgeStarBudgetMatrix](EdgeStarBudgetMatrix.md)
