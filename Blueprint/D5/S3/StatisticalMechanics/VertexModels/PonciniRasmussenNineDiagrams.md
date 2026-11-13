# Nine-strand matching coordinates

## Abstract

Nine-strand matching coordinates

There are 4862 indexed noncrossing matchings. The actual private matching and transitions constants supply the decoded involution and literal transition tree. Both tables use D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.Tree and its shared get function. Circular order lists top ports left to right and bottom ports right to left. Transition value 4862 denotes a loop.

**Definition 1.1 (diagram).**

$$\forall (i: \operatorname{Fin}\left(4862\right)), (\operatorname{diagram}\left(i\right) = \operatorname{Subtype}.\operatorname{mk}\left(\operatorname{toMatching}\left(\operatorname{matching}\left(i\right)\right), \operatorname{Exists}.\operatorname{intro}\left(\operatorname{matching}\left(i\right), \operatorname{rfl}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.diagram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype pairs the literal matching with its noncrossing representative.

**Definition 1.2 (transition).**

$$\forall (g: \operatorname{Fin}\left(8\right)), (\forall (i: \operatorname{Fin}\left(4862\right)), (\operatorname{transition}\left(g, i\right) = \operatorname{Fin}.\operatorname{mk}\left(\operatorname{Nat}.\operatorname{mod}\left(\operatorname{Nat}.\operatorname{div}\left(\operatorname{get}\left(\operatorname{get}\left(\operatorname{transitions}, \operatorname{Fin}.\operatorname{val}\left(i\right)\right), 0\right), (4863)^{(\operatorname{Fin}.\operatorname{val}\left(g\right))}\right), 4863\right), \operatorname{Nat}.\operatorname{mod_{lt}}\left(\operatorname{Nat}.\operatorname{div}\left(\operatorname{get}\left(\operatorname{get}\left(\operatorname{transitions}, \operatorname{Fin}.\operatorname{val}\left(i\right)\right), 0\right), (4863)^{(\operatorname{Fin}.\operatorname{val}\left(g\right))}\right), \operatorname{by} \operatorname{omega}\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both operations on the packed transition code are natural-number division and remainder.

**Theorem 1.3 (transition_check).**

$$\forall (i: \operatorname{Fin}\left(4862\right)), (\forall (g: \operatorname{Fin}\left(8\right)), (((\operatorname{Matching}.\operatorname{mate}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{diagram}\left(i\right)\right), \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(g\right), \operatorname{by} \operatorname{omega}\right)\right)\right) = \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(g\right)) + (1), \operatorname{by} \operatorname{omega}\right)\right)) \Leftrightarrow (\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right) = 4862)) \land (\forall (ht: \operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right) < 4862), (\forall (x: \operatorname{Boundary}\left(9\right)), (\operatorname{Matching}.\operatorname{mate}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{diagram}\left(\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right), ht\right)\right)\right), x\right) = \operatorname{reconnected}\left(\operatorname{Fin}.\operatorname{val}\left(g\right), \operatorname{by} \operatorname{omega}, \operatorname{Subtype}.\operatorname{val}\left(\operatorname{diagram}\left(i\right)\right), x\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target is constructed in Fin 4862 using ht. The source port indices lie in Fin 9 because g lies in Fin 8.

**Theorem 1.4 (unit_check).**

$$\forall (x: \operatorname{Boundary}\left(9\right)), (\operatorname{Matching}.\operatorname{mate}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{diagram}\left(\operatorname{Fin}.\operatorname{mk}\left(4861, \operatorname{by} \operatorname{omega}\right)\right)\right), x\right) = \operatorname{Matching}.\operatorname{mate}\left(\operatorname{identityMatching}\left(9\right), x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.unit_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate 4861 has the mate function of the identity matching.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.diagram`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition_check`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.unit_check`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore](../../Combinatorics/PerfectMatchings/OrderedMatchingCore.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra](../../Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/PlanarSewing](../../Combinatorics/PerfectMatchings/PlanarSewing.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree](PonciniRasmussenCertificateTree.md)
- Dependency: [D5/S3/Topology/CupCapComposition](../../Topology/CupCapComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](../../Topology/FiniteMatchingClosure.md)
