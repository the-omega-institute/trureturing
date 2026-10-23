# Critical six-occurrence signature words

## Abstract

A critical six-occurrence low edge has no adjacent two-count signatures and at most one such face.

Use the raw face pairing and valid coloring on arbitrary finite T. Prefix notation for the constructed edge star is as in the budget statement. Fiber(s,e) contains occurrences, not distinct neighbour labels; val(i) is its underlying occurrence and snd(val(i)) its local edge. edgeDegree is the fiber cardinality, fourHighCount counts occurrences with four high neighbours, and twoFaceCount counts true signatures. The low edge has six occurrences, every occurrence has at least three high neighbours and at least four have four high neighbours. No equality of global opposite labels, manifold-link certification, continuous angle margin or geometric closure is asserted.

**Theorem 1.1 (Classification, endpoint parity and the cyclic word).**

$$\forall T \in Type, p \in RawFacePairing\left(T\right), color \in GlobalEdge\left(p\right) \to Bool, valid \in ValidColoring\left(p, color\right), e \in GlobalEdge\left(p\right),\; Fintype\left(T\right) \Rightarrow \left(color\left(e\right) = true \Rightarrow \left(\left(\forall i \in Fiber\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right),\; 3 \le highNeighbourCount\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), val\left(i\right)\right), snd\left(val\left(i\right)\right)\right)\right) \Rightarrow \left(edgeDegree\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) = 6 \Rightarrow \left(4 \le fourHighCount\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) \Rightarrow \left(\left(\forall i \in Fiber\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right),\; \left(highNeighbourCount\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), val\left(i\right)\right), snd\left(val\left(i\right)\right)\right) = 4 \land colorCard\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), val\left(i\right)\right), snd\left(val\left(i\right)\right)\right) = 2\right) \lor \left(highNeighbourCount\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), val\left(i\right)\right), snd\left(val\left(i\right)\right)\right) = 3 \land isPathEnd\left(localColor\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), val\left(i\right)\right), snd\left(val\left(i\right)\right)\right)\right)\right) \land \left(\left(pathEndCount\left(p, color, valid, e\right) = 0 \lor pathEndCount\left(p, color, valid, e\right) = 2\right) \land \left(\left(\forall i \in Fiber\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right),\; \neg \left(signature\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), val\left(i\right)\right) = true \land signature\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), next\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), val\left(i\right)\right)\right) = true\right)\right) \land twoFaceCount\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) \le 1\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/CriticalEdgeSignatureWord.critical_edge_signature_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite local classification permits only the four-high/color-cardinality-two case or the three-high/path-end case. At least four four-high occurrences leave at most two path ends. Actual edge balance forces their number to be zero or two. No occurrence has a true-to-true transition; counting false-to-true transitions then bounds the number of true signatures by one.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/CriticalEdgeSignatureWord.critical_edge_signature_word`
- Dependency: [D5/S3/Geometry/Hyperideal/EdgeStarBudgetMatrix](EdgeStarBudgetMatrix.md)
