# Checked nine-strand matching coordinates

## Abstract

Checked nine-strand matching coordinates

There are 4862 indexed literal matchings. Raw partner data are packed as base-18 integers: the digit at position x is the partner of x. The circular boundary lists the top ports left to right and the bottom ports right to left. All involution, no-fixed-point, noncrossing and transition facts are checked by kernel reduction. No completeness or faithful-representation assertion is needed.

**Definition 1.1 (diagram).**

$$\forall i \in \operatorname{Fin}\left(4862\right),\; \operatorname{diagram}\left(i\right) = \operatorname{Subtype}\left(\operatorname{toMatching}\left(\operatorname{matching}\left(i\right)\right), \operatorname{ExistsWitness}\left(\operatorname{matching}\left(i\right), rfl\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.diagram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matching(i) is the NCMatching with the decoded partner function and the checked validity proofs.

**Definition 1.2 (transition).**

$$\forall g \in \operatorname{Fin}\left(8\right),\; \forall i \in \operatorname{Fin}\left(4862\right),\; \operatorname{transition}\left(g, i\right) = \operatorname{Modulo}\left(\operatorname{Divide}\left(\operatorname{get}\left(\operatorname{get}\left(transitions, \operatorname{val}\left(i\right)\right), 0\right), \operatorname{Power}\left(4863, \operatorname{val}\left(g\right)\right)\right), 4863\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The code 4862 denotes a loop and hence zero. Other codes denote the reconnected target diagram. IndexBound is the finite-index inequality supplied by the generator type.

**Theorem 1.3 (transition_check).**

$$\forall i \in \operatorname{Fin}\left(4862\right),\; \forall g \in \operatorname{Fin}\left(8\right),\; \left(\operatorname{mate}\left(\operatorname{val}\left(\operatorname{diagram}\left(i\right)\right), \operatorname{Pair}\left(False, \operatorname{val}\left(g\right)\right)\right) = \operatorname{Pair}\left(False, \operatorname{Add}\left(\operatorname{val}\left(g\right), 1\right)\right) \Leftrightarrow \operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right) = 4862\right) \land \left(\forall ht \in \operatorname{Less}\left(\operatorname{val}\left(\operatorname{transition}\left(g, i\right)\right), 4862\right),\; \forall x \in \operatorname{Boundary}\left(9\right),\; \operatorname{mate}\left(\operatorname{val}\left(\operatorname{diagram}\left(\operatorname{CastFin}\left(\operatorname{transition}\left(g, i\right), ht\right)\right)\right), x\right) = \operatorname{reconnected}\left(\operatorname{val}\left(g\right), IndexBound, \operatorname{val}\left(\operatorname{diagram}\left(i\right)\right), x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two generator ports are paired precisely for a zero transition. Each nonzero target has exactly the reconnected partner function.

**Theorem 1.4 (unit_check).**

$$\forall x \in \operatorname{Boundary}\left(9\right),\; \operatorname{mate}\left(\operatorname{val}\left(\operatorname{diagram}\left(4861\right)\right), x\right) = \operatorname{mate}\left(\operatorname{identityMatching}\left(9\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.unit_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The last coordinate is the actual through-strand identity matching.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.diagram`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition_check`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.unit_check`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore](../../Combinatorics/PerfectMatchings/OrderedMatchingCore.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra](../../Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/PlanarSewing](../../Combinatorics/PerfectMatchings/PlanarSewing.md)
- Dependency: [D5/S3/Topology/CupCapComposition](../../Topology/CupCapComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](../../Topology/FiniteMatchingClosure.md)
