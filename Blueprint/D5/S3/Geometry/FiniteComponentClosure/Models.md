# Models

## Abstract

Coordinate bouquets retain every positive-dimensional sphere occurrence and empty lists as points. Their finite disjoint unions model all nonempty finite component types. Native vertex gluing is identified with its actual quotient wedge.

Coordinate bouquets retain every positive-dimensional sphere occurrence and empty lists as points. Their finite disjoint unions model all nonempty finite component types. Native vertex gluing is identified with its actual quotient wedge.

**Definition 1.1 (Finite positive-sphere bouquets).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/Models.bouquetComplex`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/Models.bouquetComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A BouquetSpec is a finite list of positive sphere dimensions, counted with repetitions. Each native sphere is embedded with its selected vertex identified with one common coordinate vertex. The empty list is a single actual vertex and therefore one point component.

**Definition 1.2 (The actual bouquet quotient).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/Models.bouquetQuotientHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/Models.bouquetQuotientHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The disjoint union of the finite sphere family and a separate common point, with precisely the repeated sphere basepoints and common point collapsed, is homeomorphic to the coordinate bouquet. The quotient kernel and surjectivity include the empty family.

**Definition 1.3 (Standard sphere quotient presentation).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/Models.standardBouquetHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/Models.standardBouquetHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native finite bouquet is homeomorphic to the actual quotient bouquet of standard Euclidean spheres. Each sphere homeomorphism transports its specified basepoint, so this is an identification of actual quotient spaces.

**Definition 1.4 (All finite components).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/Models.normalComplex`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/Models.normalComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normal model is the tagged disjoint union of m coordinate bouquets. Different empty lists give different point components; no point component is deleted.

**Definition 1.5 (The tagged coproduct homeomorphism).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/Models.normalHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/Models.normalHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate realization of the normal complex is homeomorphic to the sigma type of its bouquet realizations, with their coproduct topology. The canonical normalPoint is the common vertex of the selected tagged bouquet.

**Definition 1.6 (Nonempty finite component homotopy types).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/Models.WPlus`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/Models.WPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

WPlus K means that the realization of K is homotopy equivalent to a normalComplex with a positive finite component count and a finite positive-sphere list for each component. Lists may be empty. This definition does not assert an arbitrary-index reduction.

## References

- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/Models.WPlus`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/Models.bouquetComplex`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/Models.bouquetQuotientHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/Models.normalComplex`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/Models.normalHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/Models.standardBouquetHomeomorph`
- Dependency: [D5/S3/Geometry/FiniteComponentClosure/Transport](Transport.md)
