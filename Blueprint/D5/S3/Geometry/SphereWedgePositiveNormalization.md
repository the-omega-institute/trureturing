# Pointed sphere wedge normalization

## Abstract

Ordinary pointed sphere wedges admit actual positive-bouquet and isolated-point normal forms.

**Definition 1.1 (Positive sphere indices).**

Lean statement: `D5/S3/Geometry/SphereWedgePositiveNormalization.PositiveIndex`

*Formalization.* `D5/S3/Geometry/SphereWedgePositiveNormalization.PositiveIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary J and dimensions n:J to Nat, PositiveIndex consists of j with 0<n(j). No connected-component assertion is built into this subtype.

**Definition 1.2 (One isolated point per zero sphere).**

Lean statement: `D5/S3/Geometry/SphereWedgePositiveNormalization.ZeroIndex`

*Formalization.* `D5/S3/Geometry/SphereWedgePositiveNormalization.ZeroIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ZeroIndex is the subtype n(j)=0, equipped with the discrete topology. Every such index is retained, regardless of the size of the family.

**Definition 1.3 (The genuine positive quotient bouquet).**

Lean statement: `D5/S3/Geometry/SphereWedgePositiveNormalization.PositiveWedge`

*Formalization.* `D5/S3/Geometry/SphereWedgePositiveNormalization.PositiveWedge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use CompactWedgeFiniteFactor.FamilyWedge with the original positive sphere dimensions and EuclideanSphereJoin.coordinatePoint basepoints. Its extra Unit representative retains the common point when there are no positive factors.

**Definition 1.4 (Actual continuous maps and both inverse identities).**

Lean statement: `D5/S3/Geometry/SphereWedgePositiveNormalization.normalizationHomeomorph`

*Formalization.* `D5/S3/Geometry/SphereWedgePositiveNormalization.normalizationHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary supplied sphere points b(j), reflect in the orthogonal complement of the span of b(j)-coordinatePoint(n(j)). Public Mathlib Submodule.reflection_sub sends b(j) exactly to the coordinate point, even when these vectors coincide. The linear isometry restricts to the actual unit sphere. In dimension zero, EuclideanSpace.sphere_zero_eq and the scalar square equation give precisely the two coordinate poles. The resulting finite T1 sphere is discrete. On a positive factor, send the normalized sphere point to its positive-bouquet class; on a zero factor send the coordinate pole to the common basepoint and the opposite pole to its ZeroIndex point. The extra Unit representative also maps to the common basepoint. These maps descend through the actual quotient relation. The inverse includes positive factors after the inverse reflection, and sends each zero index to its opposite pole after the inverse reflection. Continuity follows factorwise from the coproduct and quotient universal properties; both identities are proved on raw representatives. No quotient/subspace topology identification, arbitrary unbased wedge equivalence, finiteness assumption, homology or noncontractibility is used. All-zero families retain the basepoint and one additional isolated point for every factor; the empty family retains one point. This elementary construction is RepoDerived, without a novelty or exact literature-attestation claim.

**Theorem 1.5 (The basepoint remains in the positive bouquet).**

Lean statement: `D5/S3/Geometry/SphereWedgePositiveNormalization.normalization_base`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SphereWedgePositiveNormalization.normalization_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalization sends the original common basepoint exactly to the left summand's common basepoint. This equality is consumed by the pointed dependent-coproduct endpoint.

**Definition 1.6 (Pointed dependent outer coproduct normalization).**

Lean statement: `D5/S3/Geometry/SphereWedgePositiveNormalization.coproductNormalizationHomeomorph`

*Formalization.* `D5/S3/Geometry/SphereWedgePositiveNormalization.coproductNormalizationHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary dependent outer and inner families, apply the one-wedge homeomorphism in each outer summand and distribute the dependent coproduct over the two summands. The result bundles an actual homeomorphism to the coproduct of positive bouquets plus the dependent coproduct of zero indices, together with its exact action on every original outer basepoint. Both distribution maps are continuous by the native coproduct universal properties. Empty positive selections retain one point for every original outer index, while an empty outer type stays empty. Finite selected original indices from CompactWedgeFiniteFactor therefore yield finite normal-form indices without asserting that the unselected original indices were finite. This endpoint supplies the normalization step of the Carnero Bravo Question 22 route; the full composition-closure question remains separate and unresolved here.

## References

- Truth anchor: `D5/S3/Geometry/SphereWedgePositiveNormalization.PositiveIndex`
- Truth anchor: `D5/S3/Geometry/SphereWedgePositiveNormalization.PositiveWedge`
- Truth anchor: `D5/S3/Geometry/SphereWedgePositiveNormalization.ZeroIndex`
- Truth anchor: `D5/S3/Geometry/SphereWedgePositiveNormalization.coproductNormalizationHomeomorph`
- Truth anchor: `D5/S3/Geometry/SphereWedgePositiveNormalization.normalizationHomeomorph`
- Truth anchor: `D5/S3/Geometry/SphereWedgePositiveNormalization.normalization_base`
- Dependency: [D5/S3/Geometry/CompactWedgeFiniteFactor](CompactWedgeFiniteFactor.md)
- Dependency: [D5/S3/Geometry/EuclideanSphereJoin](EuclideanSphereJoin.md)
