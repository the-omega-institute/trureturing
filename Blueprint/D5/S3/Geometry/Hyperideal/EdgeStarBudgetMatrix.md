# Actual edge-star budget matrices

## Abstract

The low and high budgets equal weighted transition totals on the actual edge class.

Quantify over an arbitrary finite tetrahedron type T, raw involutive face pairing p, color on p.GlobalEdge, valid coloring and e:p.GlobalEdge. In prefix notation, edgeStars(toFacePairedTriangulation(p,color,valid)) is the constructed s, not a free edge star. SameCycle(next(s),i,j) is the cycle relation of that permutation. False denotes face count one, true face count two. beta(4)=arccos(17/33), beta(3)=arccos(49 sqrt(6)/198), beta(2)=arccos(70/99). theta(0)=arccos(31/33), theta(1)=arccos(25/sqrt(726)), theta(2)=arccos(81/88), theta(3)=arccos(61/sqrt(4752)), theta(4)=arccos(23/27). The row/column order false,true gives lowMatrix=[[beta(4),beta(3)],[beta(3),beta(2)]] and highMatrix=[[theta(2),theta(1)],[theta(1),theta(0)]]. Each matrix total is the sum over a,b:Bool of transitionCount(s,e,a,b) times its matrix entry; each budget sums the corresponding high-neighbour weight over occurrences in Fiber(s,e).

**Theorem 1.1 (Cycle classes and both weighted budgets).**

$$\forall T \in Type, p \in RawFacePairing\left(T\right), color \in GlobalEdge\left(p\right) \to Bool, valid \in ValidColoring\left(p, color\right), e \in GlobalEdge\left(p\right),\; Fintype\left(T\right) \Rightarrow \left(\left(\forall i \in Occurrence\left(T\right), j \in Occurrence\left(T\right),\; SameCycle\left(next\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right)\right), i, j\right) \Leftrightarrow globalEdge\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), i\right) = globalEdge\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), j\right)\right) \land \left(\left(\forall i \in Occurrence\left(T\right),\; globalEdge\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), next\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), i\right)\right) = globalEdge\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), i\right)\right) \land \left(\left(color\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) = true \Rightarrow \left(lowBudget\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) = lowMatrixTotal\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) \land \left(lowBudget\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) > 2 \cdot \pi \Leftrightarrow lowMatrixTotal\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) > 2 \cdot \pi\right)\right)\right) \land \left(color\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) = false \Rightarrow \left(highBudget\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) = highMatrixTotal\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) \land \left(highBudget\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) > 2 \cdot \pi \Leftrightarrow highMatrixTotal\left(edgeStars\left(toFacePairedTriangulation\left(p, color, valid\right)\right), e\right) > 2 \cdot \pi\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/EdgeStarBudgetMatrix.actual_edge_budget_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each paired slot lies in the same successor cycle, including the case where its face is incoming, using the inverse face map. Conversely successor steps preserve the quotient label. Grouping actual occurrences by their two signatures gives both matrix identities and their exact two-pi equivalences. These are angle-budget identities, not a proof of a common geometric realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/EdgeStarBudgetMatrix.actual_edge_budget_matrix`
- Dependency: [D5/S3/Geometry/Hyperideal/EdgeStarTransitions](EdgeStarTransitions.md)
