# The quotient by the retained fair-bias realization

## Abstract

Each omitted simplex attaches to the retained realization along its full boundary.

**Theorem 1.1 (The attaching locus of an omitted simplex).**

Lean statement: `D5/S3/TotalVariation/FairBiasFacetQuotient.diskIn_mem_core_iff_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasFacetQuotient.diskIn_mem_core_iff_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A point of a full-restriction facet simplex belongs to the retained realization exactly when a coordinate indexed by a vertex of that facet is zero. This gives the entire boundary, which is empty for a singleton facet.

**Theorem 1.2 (The canonical attachment quotient).**

Lean statement: `D5/S3/TotalVariation/FairBiasFacetQuotient.exists_core_attachment_homeomorph`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasFacetQuotient.exists_core_attachment_homeomorph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the signed complex has a nonempty facet. Take the disjoint sum of one point and the coordinate simplices of the full-restriction facets. Identify every attaching boundary point with the added point. The resulting space is homeomorphic to the original realization with its retained subcomplex collapsed. The homeomorphism agrees with coordinate inclusion followed by the quotient map on each simplex and sends the added point to the retained class.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasFacetQuotient.diskIn_mem_core_iff_boundary`
- Truth anchor: `D5/S3/TotalVariation/FairBiasFacetQuotient.exists_core_attachment_homeomorph`
- Dependency: [D5/S3/Geometry/FiniteAttachmentQuotient](../Geometry/FiniteAttachmentQuotient.md)
- Dependency: [D5/S3/TotalVariation/FairBiasCriticalFacetCollapse](FairBiasCriticalFacetCollapse.md)
