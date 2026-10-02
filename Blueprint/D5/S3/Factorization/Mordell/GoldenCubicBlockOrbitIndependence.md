# Mordell Cubic Orbit Independence

## Abstract

Horizontal cubic rotations isolate coefficients in Mordell point relations.

**Theorem 1.1 (Cubic orbit coefficient elimination).**

Lean statement: `D5/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence.cubic_orbit_independent_mod_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence.cubic_orbit_independent_mod_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independent coordinate actions and the cubic trace reduce a base-field relation to a positive quadratic norm annihilating one non-torsion point; both integer coefficients vanish.

**Theorem 1.2 (Cubic orbit independence modulo base points).**

Lean statement: `D5/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence.cubic_mordell_family_independent_mod_base`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence.cubic_mordell_family_independent_mod_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Mordell curve carrying non-torsion points on independently rotated cubic coordinates, each original point and its cubic rotation are independent modulo the base-field point group. The proof uses the horizontal three-point relation and an integral quadratic norm.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence.cubic_mordell_family_independent_mod_base`
- Truth anchor: `D5/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence.cubic_orbit_independent_mod_fixed`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
- Dependency: [D5/S3/Factorization/Dedekind/GaloisScalarHeight](../Dedekind/GaloisScalarHeight.md)
- Dependency: [D5/S3/Factorization/Galois/GoldenCubicBlockPositiveRootTower](../Galois/GoldenCubicBlockPositiveRootTower.md)
- Dependency: [D5/S3/Factorization/Galois/GoldenCubicCommonInertiaAndSignature](../Galois/GoldenCubicCommonInertiaAndSignature.md)
- Dependency: [D5/S3/Factorization/Mordell/CanonicalPointHeight](CanonicalPointHeight.md)
- Dependency: [D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists](GoldenCubicBlockMordellTwists.md)
- Dependency: [D5/S3/Factorization/Mordell/PointVariableChange](PointVariableChange.md)
- Dependency: [D5/S3/Factorization/Mordell/SymmetricSquareAddition](SymmetricSquareAddition.md)
- Dependency: [D5/S3/Factorization/MordellTwoAdicNonTorsion](../MordellTwoAdicNonTorsion.md)
- Dependency: [D5/S3/QuadraticForms/ParallelogramConstruction](../../QuadraticForms/ParallelogramConstruction.md)
