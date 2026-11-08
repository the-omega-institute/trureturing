# Conjecture B.1 for literal diagram algebras

## Abstract

Conjecture B.1 for literal diagram algebras

The coefficient field is C and the element is the negative sum h(C,n) of all n-1 standard generators. The multiplication is actual path concatenation of noncrossing matching diagrams, with every internal loop assigned zero. The definition below preserves the original universal quantifier. The degree-57 monic integer annihilator is transported through the exact generator action to the complex diagram algebra. Minpoly minimality gives degree at most 57, contradicting the conjectured value 81 at n=9. No faithful-representation assumption is used.

**Definition 1.1 (claim).**

$$claim \Leftrightarrow \left(\forall n \in Nat,\; \operatorname{AtLeast}\left(n, 2\right) \Rightarrow \operatorname{RationalCast}\left(\operatorname{natDegree}\left(\operatorname{minpoly}\left(Complex, \operatorname{h}\left(Complex, n\right)\right)\right)\right) = \operatorname{Divide}\left(\operatorname{Add}\left(\operatorname{Power}\left(3, \operatorname{Divide}\left(\operatorname{Add}\left(n, 1\right), 2\right)\right), \operatorname{Multiply}\left(\operatorname{Power}\left(\operatorname{NegativeOne}\left(\right), n\right), \operatorname{Power}\left(3, \operatorname{Divide}\left(\operatorname{Subtract}\left(n, 1\right), 2\right)\right)\right)\right), 2\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The powers use natural-number exponents with natural division by two; the outer equality is in Q.

**Theorem 1.2 (result).**

$$\operatorname{Not}\left(claim\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer Horner certificate, the literal diagram transition law, and the unit diagram yield p(h_9)=0. The polynomial is monic of degree 57, so minpoly has degree at most 57<81.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra](../../Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction](PonciniRasmussenNineAction.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams](PonciniRasmussenNineDiagrams.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges](PonciniRasmussenNineEdges.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHorner](PonciniRasmussenNineHorner.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
