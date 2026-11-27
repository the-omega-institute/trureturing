# Reduced integral homology of the signed fair-bias complex

## Abstract

The full-restriction facets index a basis for the only possible nonzero reduced homology group.

**Theorem 1.1 (Homology of the original realization in every nonnegative degree).**

Lean statement: `D5/S3/TotalVariation/FairBiasIntegralHomology.reducedHomology_eq_fullRestrictionFacets`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasIntegralHomology.reducedHomology_eq_fullRestrictionFacets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Allen Hatcher (2002). *Algebraic Topology*. URL: <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>.

*Commentary.*

Take a finite family of columns in a finite binary vector space and fix a linear order on the signed labels. The signed fair-bias complex has free reduced integral singular homology in column nullity minus one, using natural subtraction. The summands are indexed by the facets equal to their restriction faces. Every other nonnegative degree vanishes. If there are no nonempty facets, the realization and index are empty, so every nonnegative degree vanishes.

When a facet exists, the core quotient carries the homology of the original realization to its sphere wedge. For positive degrees, a based homeomorphism separates one factor from the wedge of the remaining factors. Stereographic projection gives contractions fixed at their basepoints, and the binary Mayer–Vietoris splitting adds one summand at each step, as in Hatcher’s wedge-sum argument in Corollary 2.25. A sphere contributes its coefficient group only in its own degree.

In degree zero, a positive-dimensional sphere wedge is path connected. A wedge of zero-spheres is identified by the pointed sphere-wedge normalization with one point for each factor in addition to the common point. The augmentation kernel has one generator for each of those other components. An empty family gives a point and every reduced group vanishes.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasIntegralHomology.reducedHomology_eq_fullRestrictionFacets`
- Dependency: [D5/S3/Geometry/CompactWedgeFiniteFactor](../Geometry/CompactWedgeFiniteFactor.md)
- Dependency: [D5/S3/Geometry/EuclideanSphereJoin](../Geometry/EuclideanSphereJoin.md)
- Dependency: [D5/S3/Geometry/FiniteComponentClosure/BasedJoin](../Geometry/FiniteComponentClosure/BasedJoin.md)
- Dependency: [D5/S3/Geometry/FiniteFamilyWedgeSplit](../Geometry/FiniteFamilyWedgeSplit.md)
- Dependency: [D5/S3/Geometry/SphereWedgePositiveNormalization](../Geometry/SphereWedgePositiveNormalization.md)
- Dependency: [D5/S3/Topology/PointedWedgeHomology](../Topology/PointedWedgeHomology.md)
- Dependency: [D5/S3/Topology/SphereHomologyAllDegrees](../Topology/SphereHomologyAllDegrees.md)
- Dependency: [D5/S3/TotalVariation/FairBiasSphericalWedge](FairBiasSphericalWedge.md)
