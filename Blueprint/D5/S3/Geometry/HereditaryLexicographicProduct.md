# Hereditary lexicographic product

## Abstract

Unsuspended hereditary sphere-wedge coproduct types for actual lexicographic graph products.

**Definition 1.1 (The source's unsuspended SP alternatives).**

Lean statement: `D5/S3/Geometry/HereditaryLexicographicProduct.sourceSP`

*Formalization.* `D5/S3/Geometry/HereditaryLexicographicProduct.sourceSP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For an actual topological space X, sourceSP is ContractibleSpace X or the existence of an arbitrary index type J, natural sphere dimensions d(j), actual sphere points q(j), and an actual homotopy equivalence X to CompactWedgeFiniteFactor.FamilyWedge q. The quotient identifies all supplied sphere points with its additional common point. J is not assumed finite; dimensions may be zero; an empty J gives a point. SP is not a suspension operator.

**Definition 1.2 (The source's three P alternatives).**

Lean statement: `D5/S3/Geometry/HereditaryLexicographicProduct.sourceP`

*Formalization.* `D5/S3/Geometry/HereditaryLexicographicProduct.sourceP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

P permits SP or an actual homotopy equivalence to an arbitrary dependent coproduct of ordinary sphere wedges. Both original outer and inner index families are unrestricted. In particular an empty outer type gives the empty space, whereas each empty inner family gives a point component. This is the contractible, wedge, or disjoint union of wedges classification in Section 2 of Carnero Bravo arXiv:2505.06457v2.

**Definition 1.3 (The explicit empty-induced convention for hereditary SP).**

Lean statement: `D5/S3/Geometry/HereditaryLexicographicProduct.sourceSW`

*Formalization.* `D5/S3/Geometry/HereditaryLexicographicProduct.sourceSW` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every nonempty induced vertex set S, require sourceSP of the actual native independence realization of G.induce S. The native realization of the vertexless graph is empty, while contractible spaces and ordinary wedges are nonempty. Consequently a literal all-subsets SP predicate with only these nonempty alternatives would make every SW assumption impossible. This definition states the nonempty-induced convention explicitly, without adding an empty sphere to SP or a suspension. The paper states any induced subgraph without separately resolving this boundary; excluding the vertexless input, or separately allowing its augmented empty model, gives the same nonempty obligations. The output theorem handles the vertexless target separately by an actual empty outer coproduct.

**Definition 1.4 (Hereditary P includes every induced subset).**

Lean statement: `D5/S3/Geometry/HereditaryLexicographicProduct.sourceW`

*Formalization.* `D5/S3/Geometry/HereditaryLexicographicProduct.sourceW` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every induced vertex set S, including the empty one, require sourceP of the actual independence realization. The empty target is covered by the disjoint-union alternative with zero outer summands, so no nonemptiness assumption is imposed on output subsets.

**Definition 1.5 (The graph on the actual product vertex type).**

Lean statement: `D5/S3/Geometry/HereditaryLexicographicProduct.lexicographicProduct`

*Formalization.* `D5/S3/Geometry/HereditaryLexicographicProduct.lexicographicProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

On V times U, adjacency is an outer G edge, or equality of the outer coordinates together with an inner H edge. This is exactly the product edge set in the primary source. An explicit sigma-to-product graph isomorphism, restricted by Mathlib SimpleGraph.Iso.induce, connects it to the heterogeneous substitution graph.

**Theorem 1.6 (The complete unsuspended hereditary product conclusion).**

Lean statement: `D5/S3/Geometry/HereditaryLexicographicProduct.result`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HereditaryLexicographicProduct.result` (`✓ std3`). ∎

*Resolves.* `Problems/carnero-bravo-2025-hereditary-lexicographic-products` (proved) by `D5/S3/Geometry/HereditaryLexicographicProduct.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"carnero-bravo-2025-hereditary-lexicographic-products","declaration_gid":"D5/S3/Geometry/HereditaryLexicographicProduct.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For all finite vertex types V,U in any common universe, simple graphs G,H with their original orders at least two, and sourceSW hypotheses on both factors, sourceW holds for the actual lexicographicProduct G H. The two order hypotheses remain in the facade; the underlying stronger substitution induction does not need them. The sphere-model indices in either input may be arbitrary and may live in separate universes. The output has actual finite outer and inner sphere witnesses. No endpoint, WPlus predicate, join closure, wedge closure, HEP or native-model identification appears among the facade's hypotheses. For a nonempty selected product set, transport it through the actual sigma/product isomorphism. OccupiedFiberSubstitution.independenceHomeomorph then identifies its independence realization with substitution over exactly the occupied base vertices and actual nonempty selected fibers. Original unselected or empty fibers impose no extra premise. Heredity on the occupied base is transported through nestedInduceIso and its actual image in the original base; each selected fiber inherits unsuspended SP from H. Compactness of every native finite realization and its actual singleton vertex allow CompactSphereNormalForm.compactWedgeModel, compactModel and contractibleModel to produce finite sphere-list models without assuming finiteness of either original index family. nativeModelHomeomorph supplies the actual native WPlus witnesses. Use the unchanged hereditarySubstitutionCore once. Its homotopy input is composition of equivalences, its point input is the one-empty-bouquet contractible model, its ordinary-join input is the actual finiteComponentJoinClosure followed by the native ordinary/simplicial join homeomorphism, and its coordinate-vertex wedge input is selectedVertexWedgeClosure followed by the original quotient/native vertex-gluing homeomorphism. An actual coordinate vertex is proved to be a singleton face before the wedge closure is applied. The original induction handles an empty current link with the augmented simplicial unit, not an ordinary join with an empty factor. Finally transport the finite native model back to the actual sphere coproduct to obtain sourceP. For an empty selected product set, prove its native realization empty from the nonempty-face convention and use CompactSphereNormalForm.emptyModel with zero outer components. This branch never substitutes a point for the empty space. The statement is the affirmative unsuspended Question 22 conclusion under the explicitly stated empty-induced convention. Theorem 21 of the source establishes only a suspended conclusion. This implementation asserts no literature novelty or official acceptance; repository admission and the source-readout audit remain separate. The same-author Reg mirror reconstructs the complete telescope. Its attempted truth-valued dependent-family readout is proved constant on valid inputs and therefore cannot supply observational dependence; issue 22742 records the unfinished audit. A different lawful enrolled readout and a current binding certificate are still required for a validated registration.

## References

- Truth anchor: `D5/S3/Geometry/HereditaryLexicographicProduct.lexicographicProduct`
- Truth anchor: `D5/S3/Geometry/HereditaryLexicographicProduct.result`
- Truth anchor: `D5/S3/Geometry/HereditaryLexicographicProduct.sourceP`
- Truth anchor: `D5/S3/Geometry/HereditaryLexicographicProduct.sourceSP`
- Truth anchor: `D5/S3/Geometry/HereditaryLexicographicProduct.sourceSW`
- Truth anchor: `D5/S3/Geometry/HereditaryLexicographicProduct.sourceW`
- Dependency: [D5/S3/Geometry/CompactSphereNormalForm](CompactSphereNormalForm.md)
- Dependency: [D5/S3/Geometry/OccupiedFiberSubstitution](OccupiedFiberSubstitution.md)
