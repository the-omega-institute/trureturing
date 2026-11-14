# BasedJoin

## Abstract

A cone collapse is rebased at a native vertex while its quotient map remains unchanged. Exact collapsed-cone traces give relative inverse homotopies and assemble the two-component, common-vertex, and finite-family join decompositions.

A cone collapse is rebased at a native vertex while its quotient map remains unchanged. Exact collapsed-cone traces give relative inverse homotopies and assemble the two-component, common-vertex, and finite-family join decompositions.

**Definition 1.1 (Composition of based equivalences).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/BasedJoin.basedTrans`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/BasedJoin.basedTrans` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For topological spaces X,Y,Z, points x:X,y:Y,z:Z, and E:SingletonRetractionBasedInverse.BasedEquivalence x y and F:SingletonRetractionBasedInverse.BasedEquivalence y z, basedTrans E F has continuous forward map F.forward.comp E.forward and backward map E.backward.comp F.backward. These send x to z and z to x. The backward-forward composite is homotopic to id X relative to {x}, and the forward-backward composite to id Z relative to {z}. The left homotopy precomposes F.left by E.forward, postcomposes by E.backward, then concatenates E.left; the right homotopy precomposes E.right by F.backward, postcomposes by F.forward, then concatenates F.right.

**Definition 1.2 (A homeomorphism preserving the chosen point).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/BasedJoin.basedHomeomorphism`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/BasedJoin.basedHomeomorphism` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For topological spaces X,Y, e:X ≃ₜ Y, x:X, y:Y, and h:e x = y, basedHomeomorphism e x y h is a SingletonRetractionBasedInverse.BasedEquivalence x y. Its continuous maps are e and e.symm, with point laws e x = y and e.symm y = x. Its inverse homotopies are the constant identity homotopies, cast along the homeomorphism inverse equations, relative to {x} and {y}.

**Definition 1.3 (Bool as the two coordinate vertices).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/BasedJoin.boolTwoPointHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/BasedJoin.boolTwoPointHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

boolTwoPointHomeomorph : Bool ≃ₜ FiniteSimplicialJoin.Space twoPoints sends b to the vertex with coordinate function Pi.single b 1, where twoPoints is the complex on Bool whose faces have cardinality one. Its inverse returns the unique vertex label, so the vertices at false and true return false and true respectively. The discrete topology on Bool makes this bijection continuous; compactness of Bool and the Hausdorff realization give a homeomorphism.

## References

- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/BasedJoin.basedHomeomorphism`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/BasedJoin.basedTrans`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/BasedJoin.boolTwoPointHomeomorph`
- Dependency: [D5/S3/Geometry/FiniteComponentClosure/SelectedWedge](SelectedWedge.md)
