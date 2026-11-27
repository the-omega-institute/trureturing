# Quotients of finite attachment families

## Abstract

Collapsing a closed core in a finite cover identifies exactly the attachment points over it.

**Theorem 1.1 (The canonical quotient of the attachment family).**

Lean statement: `D5/S3/Geometry/FiniteAttachmentQuotient.exists_homeomorph`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAttachmentQuotient.exists_homeomorph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A compact Hausdorff space is covered by a closed core and the images of finitely many compact spaces under continuous injections. Fix a point of the core and suppose intersections of distinct attachment images lie in the core. In the disjoint sum of the attachment spaces and an added point, identify with that point each attachment point mapping into the core. The resulting quotient is homeomorphic to the ambient space with the core collapsed. On each attachment the map is the given injection followed by the ambient collapse. It maps the added point to the core class. The construction permits an empty index and attachments disjoint from the core.

## References

- Truth anchor: `D5/S3/Geometry/FiniteAttachmentQuotient.exists_homeomorph`
- Dependency: [D5/S3/Geometry/FiniteConeUnionWedge](FiniteConeUnionWedge.md)
