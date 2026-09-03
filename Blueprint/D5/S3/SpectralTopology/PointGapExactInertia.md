# Point-Gap Exact Inertia

## Abstract

A finite point gap gives exact half-dimensional chiral inertia.

**Theorem 1.1 (Point-gap exact zero-scale inertia).**

$$\operatorname{posIndex}(\operatorname{localizerZero}(X, H, x, z)) = \operatorname{card}(n) \land \operatorname{negIndex}(\operatorname{localizerZero}(X, H, x, z)) = \operatorname{card}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/PointGapExactInertia.zero_scale_localizer_inertia_of_point_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive and negative inertia counts of a finite Hermitian matrix add to its rank, and a finite point gap gives the zero-scale localizer full rank on the doubled carrier.

Combined with the frozen chiral inertia balance, the positive and negative zero-scale counts therefore both equal the original carrier cardinality: under a point gap there are no zero modes, and the doubled finite spectrum splits into equally many positive and negative eigenvalues.

## References

- Truth anchor: `D5/S3/SpectralTopology/PointGapExactInertia.zero_scale_localizer_inertia_of_point_gap`
- Dependency: [D5/S3/SpectralTopology/FiniteSpectralLocalizer](FiniteSpectralLocalizer.md)
