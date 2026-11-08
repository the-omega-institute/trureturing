# Exact action in the diagram algebra

## Abstract

Exact action in the diagram algebra

R is any commutative coefficient ring. The statements concern multiplication in TL(R,9), whose basis contains every noncrossing boundary matching. They follow from the checked table and the general cup-cap path and loop laws.

**Theorem 1.1 (unit_basis).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \operatorname{Single}\left(R, \operatorname{diagram}\left(4861\right), 1\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.unit_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Single(R,d,r) denotes the basis vector with coefficient r in TL(R,9). The basis vector at coordinate 4861 equals the multiplicative identity.

**Theorem 1.2 (generator_basis).**

$$\forall R \in Type,\; [\operatorname{CommRing}\left(R\right)] \forall g \in \operatorname{Fin}\left(8\right),\; \forall i \in \operatorname{Fin}\left(4862\right),\; \operatorname{Multiply}\left(\operatorname{generator}\left(R, 9, g\right), \operatorname{Single}\left(R, \operatorname{diagram}\left(i\right), 1\right)\right) = \operatorname{IfLess}\left(\operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right), 4862, \operatorname{Single}\left(R, \operatorname{diagram}\left(\operatorname{transition}\left(g, i\right)\right), 1\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.generator_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every generator acts by exactly the indicated target basis vector, or by zero when an internal loop is formed.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.generator_basis`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.unit_basis`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra](../../Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams](PonciniRasmussenNineDiagrams.md)
- Dependency: [D5/S3/Topology/CupCapComposition](../../Topology/CupCapComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](../../Topology/FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](../../Topology/FiniteMatchingComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingSewing](../../Topology/FiniteMatchingSewing.md)
