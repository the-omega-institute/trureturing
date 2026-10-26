# Periodic integration by parts and closed-slab calculus

## Abstract

Periodic integration by parts and closed-slab calculus

**Theorem 1.1 (Periodic integration by parts and closed-slab calculus).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/PeriodicDensityCalculus.periodic_haar_ibp`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/PeriodicDensityCalculus.periodic_haar_ibp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integration-by-parts theorem pairs an actual periodic scalar field with an actual periodic vector field. Coordinate boundary terms cancel because opposite faces project to the same torus point. The statement includes the empty coordinate type.

Coordinate peeling and periodic box integration by parts adapt the authenticated CoarseGraining source at commit c7ddd76 to pinned Mathlib. Authenticated Tau Ceti declarations supply compact parameter integration. The supplier licenses and attributions accompany the delivery. The compact parameter integration theorem differentiates relative to the closed time slab, so no extension in time is assumed.

The chemical-potential gradient and flux-divergence identities use the representative-defined original operators. These identities are consumed by the weak transport law. This module does not assert density pushforward or differentiability of the flow.

## References

- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/PeriodicDensityCalculus.periodic_haar_ibp`
- Dependency: [D5/S3/Geometry/ProbabilityTransport/PeriodicDensityModel](PeriodicDensityModel.md)
