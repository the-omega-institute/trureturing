# Exact action in the diagram algebra

## Abstract

Exact action in the diagram algebra

For every commutative ring R, multiplication takes place in TL(R,9) on all noncrossing boundary matchings. The last tabulated coordinate is the through-strand identity. A nonzero generator transition is a Fin 4862 index constructed from its Fin 4863 value and its strict bound.

**Theorem 1.1 (unit_basis).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] (\operatorname{MonoidAlgebra}.\operatorname{single}\left(\operatorname{diagram}\left(\operatorname{Fin}.\operatorname{mk}\left(4861, \operatorname{by} \operatorname{omega}\right)\right), 1\right): \operatorname{TL}\left(R, 9\right)) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.unit_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity coordinate represents the multiplicative unit.

**Theorem 1.2 (generator_basis).**

$$\forall (R: \operatorname{Type}), ([\operatorname{CommRing}\left(R\right)] \forall (g: \operatorname{Fin}\left(8\right)), (\forall (i: \operatorname{Fin}\left(4862\right)), (((\operatorname{generator}\left(g\right): \operatorname{TL}\left(R, 9\right))) \cdot (\operatorname{MonoidAlgebra}.\operatorname{single}\left(\operatorname{diagram}\left(i\right), 1\right)) = \operatorname{dite}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right) < 4862, ((ht: \operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right) < 4862) \mapsto \operatorname{MonoidAlgebra}.\operatorname{single}\left(\operatorname{diagram}\left(\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right), ht\right)\right), 1\right)), \operatorname{Function}.\operatorname{const}\left(\operatorname{Not}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right) < 4862\right), 0\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.generator_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The loop case gives zero; the other case gives the reconnected basis diagram.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.generator_basis`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.unit_basis`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra](../../Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams](PonciniRasmussenNineDiagrams.md)
- Dependency: [D5/S3/Topology/CupCapComposition](../../Topology/CupCapComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](../../Topology/FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](../../Topology/FiniteMatchingComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingSewing](../../Topology/FiniteMatchingSewing.md)
