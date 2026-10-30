# The actual density satisfies the moving-test transport equation

## Abstract

The actual density satisfies the moving-test transport equation

**Theorem 1.1 (The actual density satisfies the moving-test transport equation).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/SmoothDensityWeakTransport.weak_transport_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/SmoothDensityWeakTransport.weak_transport_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A C1 periodic moving test paired with the original density has the derivative given by its time derivative plus its spatial gradient paired with the actual chemical velocity, integrated against that density. The equation holds at every interior time; continuity on the closed slab is derived separately from relative smoothness.

Periodic integration by parts consumes the original Fokker–Planck equation and identifies the weak material derivative. Only one derivative of the test is used. The with-density integral identity connects the Haar pairing to the original density measures.

The finite-grid residual, discrete Grönwall estimate, and inverse-natural-number equality lemma are organizational providers. They are used by the actual Euler density and characteristic estimates in SmoothDensityEulerConsistency; arbitrary moments or a finite surrogate model are not assumptions of the public transport theorem.

## References

- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/SmoothDensityWeakTransport.weak_transport_hasDerivAt`
- Dependency: [D5/S3/Geometry/ProbabilityTransport/PeriodicDensityCalculus](PeriodicDensityCalculus.md)
