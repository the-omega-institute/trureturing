# Compact sphere source normal form

## Abstract

Compact sphere-coproduct source models admit actual finite positive sphere-list models.

**Definition 1.1 (Strictly positive sphere dimensions).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.PositiveDimension`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.PositiveDimension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An output dimension is a natural number together with its strict positivity proof. Zero-dimensional spheres are accounted for by separate point components.

**Definition 1.2 (The actual coordinate-based quotient bouquet).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.Bouquet`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.Bouquet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite list l of positive dimensions, use CompactWedgeFiniteFactor.FamilyWedge with indices Fin(l.length), factors EuclideanSphereJoin.StdSphere of dimension (l.get i).val, and coordinatePoint basepoints. The empty list has the additional distinguished representative and is exactly a one-point space. Multiplicities in the list are retained.

**Definition 1.3 (The finite outer sigma model).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.Model`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.Model` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For m natural and b:Fin m to lists of positive dimensions, Model b is the topological dependent coproduct of Bouquet(b k). It is empty when m=0. An empty inner list gives a point component rather than an absent component.

**Definition 1.4 (Output data include the actual homotopy equivalence).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.HomotopyModel`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.HomotopyModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a topological space X, the data are size m, lists b:Fin m to List PositiveDimension, and an actual X homotopy equivalent to Model b. This packages continuous maps and both inverse homotopies, not just an existential classification predicate or an assumed finite endpoint.

**Definition 1.5 (Dependent finite enumeration of a positive family).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.dimensionList`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.dimensionList` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite type J with a Fintype instance and dimension function n:J to PositiveDimension, enumerate J using Fintype.equivFin and List.ofFn. The list keeps every factor, including repeated dimensions. List.get at the induced finite index recovers the original dimension exactly.

**Definition 1.6 (Pointed quotient homeomorphism to the list).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.positiveListHomeomorph`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.positiveListHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reindex the actual sigma of spheres along the finite enumeration, casting each sphere only along the proved equality of its natural dimension. Such casts send coordinatePoint to coordinatePoint. The raw map is the identity on the additional Unit summand and the sphere reindexing on the other summand. Both the equality relation and membership in the entire collapsed basepoint subset are preserved and reflected. Apply Mathlib Homeomorph.Quotient.congr to obtain the quotient homeomorphism, bundled with its exact action on the common basepoint. Continuity and openness of sigma maps come from Mathlib; no new compact-factor engine or reflection proof is used.

**Definition 1.7 (Normalize and enumerate the selected finite sphere families).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.finiteCoproductHomeomorph`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.finiteCoproductHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite outer A and finite dependent inner families I(a), begin with SphereWedgePositiveNormalization.coproductNormalizationHomeomorph, allowing arbitrary original sphere basepoints q(a,j). Its positive bouquet in each original block is transported to a finite list by positiveListHomeomorph. Each zero-sphere index becomes one copy of the empty-list bouquet via the unique point homeomorphism. Reassemble by Equiv.sumSigmaDistrib over C=A plus Sigma a ZeroIndex(d a), then enumerate C by Fin(card C). In particular each original block contributes its positive bouquet even when its positive list is empty; each S0 factor contributes an additional isolated point; empty A stays empty. The result is an actual homeomorphism with no factor discarded.

**Definition 1.8 (The empty source uses no outer summands).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.emptyModel`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.emptyModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an empty topological source X, the output has size zero and the unique empty family of lists. Use the actual homeomorphism between empty spaces and its induced homotopy equivalence. This branch does not replace the empty space by a point.

**Definition 1.9 (Compact nonempty arbitrary source transport).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.nonemptyCompactModel`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.nonemptyCompactModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let X be compact and nonempty, with an actual homotopy equivalence to an arbitrary dependent coproduct of ordinary pointed sphere wedges. Neither original index type is required to be finite. Apply CompactWedgeFiniteFactor.finiteFactorHomotopyEquiv to obtain its actual finite selected outer and inner families. Then apply finiteCoproductHomeomorph to precisely those unchanged selected spheres and compose the equivalences. The right homotopy is supplied by the existing finite-factor construction and requires no invariant submodel assumption. The output is bundled with a proof that its outer size is positive, obtained from the finite index of the image of a source point.

**Definition 1.10 (All compact coproduct sources, including the empty branch).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.compactModel`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.compactModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any compact X and actual equivalence to the arbitrary sphere-wedge coproduct, split on source nonemptiness. Use nonemptyCompactModel in the inhabited branch and emptyModel otherwise. Contractibility, S0 factors, empty inner families and arbitrary index families are preserved. No finite-index assumption is imposed on the original source class.

**Definition 1.11 (The arbitrary single-wedge source alternative).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.compactWedgeModel`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.compactWedgeModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a compact X homotopy equivalent to one arbitrary pointed sphere wedge, first use the actual homeomorphism from that wedge to its one-summand dependent coproduct, then apply compactModel. The sphere bases are the supplied original points, and all empty and zero-dimensional inner cases remain in scope.

**Definition 1.12 (The contractible source alternative).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.contractibleModel`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.contractibleModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a ContractibleSpace X, compose Mathlib ContractibleSpace.hequiv_unit with the actual unique-point homeomorphism to the model with size one and empty bouquet list. Compactness is unnecessary for this alternative. These source adapters are intermediate work for the original unsuspended hereditary W conclusion in Carnero Bravo arXiv:2505.06457v2 Question 22. SP means contractible or homotopy equivalent to a wedge of spheres; SW quantifies that property over induced subgraphs. The native carrier maps below identify these actual source models with FiniteComponentClosure normal complexes. HereditaryLexicographicProduct consumes both directions in its final graph composition; these adapter declarations alone assert no graph closure or novelty.

**Definition 1.13 (The actual native bouquet and the coordinate sphere quotient).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.nativeBouquetHomeomorph`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.nativeBouquetHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite positive dimension list b, compose FiniteComponentClosure.standardBouquetHomeomorph with a quotient homeomorphism induced by the original spherePointHomeomorph on each sphere and the identity on the additional Unit. The native standardSphereBase is sent exactly to coordinatePoint. Equality and membership in the complete collapsed basepoint subset are preserved and reflected. This identifies the actual quotients; matching names or homotopy classifications are not used as carrier equalities. The empty list retains its one point.

**Definition 1.14 (All finite component carriers, including zero components).**

Lean statement: `D5/S3/Geometry/CompactSphereNormalForm.nativeModelHomeomorph`

*Formalization.* `D5/S3/Geometry/CompactSphereNormalForm.nativeModelHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m and family b:Fin m to lists of positive dimensions, apply FiniteComponentClosure.normalHomeomorph and then nativeBouquetHomeomorph in every sigma fiber. This is an actual homeomorphism from the native realization of normalComplex m b to Model b. It includes m=0 and point components. The source-to-native direction supplies the WPlus premises of the real finite closures, and the reverse direction supplies the arbitrary-sphere source-P conclusion of HereditaryLexicographicProduct.result.

## References

- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.Bouquet`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.HomotopyModel`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.Model`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.PositiveDimension`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.compactModel`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.compactWedgeModel`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.contractibleModel`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.dimensionList`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.emptyModel`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.finiteCoproductHomeomorph`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.nativeBouquetHomeomorph`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.nativeModelHomeomorph`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.nonemptyCompactModel`
- Truth anchor: `D5/S3/Geometry/CompactSphereNormalForm.positiveListHomeomorph`
- Dependency: [D5/S3/Geometry/FiniteComponentClosure](FiniteComponentClosure.md)
- Dependency: [D5/S3/Geometry/SphereWedgePositiveNormalization](SphereWedgePositiveNormalization.md)
