# Riemannian Critical-Line Interface

## Abstract

The existing critical-line criterion is represented by hyperbolic fixed points and zero displacement.

**Theorem 1.1 (Normal translation fixes the basepoint exactly on the critical line).**

Lean statement: `D5/S3/Zeros/RiemannianCriticalLineInterface.normal_translation_fixed_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/RiemannianCriticalLineInterface.normal_translation_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed offset Re(rho)-1/2 acts as a horizontal isometry of the real hyperbolic upper-half-space model. Its canonical basepoint is fixed exactly when the offset vanishes. This is a geometric interface and adds no zero-free hypothesis.

**Theorem 1.2 (Exact hyperbolic displacement formula).**

Lean statement: `D5/S3/Zeros/RiemannianCriticalLineInterface.normal_displacement_eq_arsinh`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/RiemannianCriticalLineInterface.normal_displacement_eq_arsinh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displacement equals 2 arsinh(|Re(rho)-1/2|/2), giving a faithful nonnegative gauge of the off-line abscissa.

**Theorem 1.3 (RH is equivalent to zero hyperbolic normal displacement of every actual zero).**

Lean statement: `D5/S3/Zeros/RiemannianCriticalLineInterface.rh_iff_all_normal_displacements_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/RiemannianCriticalLineInterface.rh_iff_all_normal_displacements_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence quantifies over the repository's actual Zeta23.IsNontrivialZero predicate and rewrites the existing RH-to-critical-line theorem. It is a reformulation, not a proof of RH.

## References

- Truth anchor: `D5/S3/Zeros/RiemannianCriticalLineInterface.normal_displacement_eq_arsinh`
- Truth anchor: `D5/S3/Zeros/RiemannianCriticalLineInterface.normal_translation_fixed_iff`
- Truth anchor: `D5/S3/Zeros/RiemannianCriticalLineInterface.rh_iff_all_normal_displacements_zero`
- Dependency: [D5/S3/Geometry/HyperbolicUpperHalfSpace](../Geometry/HyperbolicUpperHalfSpace.md)
- Dependency: [D5/S3/Zeros/ActualZeroGeometry](ActualZeroGeometry.md)
- Dependency: [D5/S3/Zeros/Symmetry/CriticalCenterCoordinate](Symmetry/CriticalCenterCoordinate.md)
