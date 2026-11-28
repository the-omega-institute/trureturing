# The native three-torsion quartic and marked cubic subfield

## Abstract

The native elliptic three-torsion quartic has an explicit cubic subfield and irreducible reduction.

**Theorem 1.1 (The quartic encodes the actual affine three-torsion).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.three_torsion_abscissa_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.three_torsion_abscissa_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the exact doubling formula on nonsingular points. Over an algebraically closed characteristic zero field, the roots are precisely the abscissas of the nonzero points killed by three.

**Theorem 1.2 (The cubic resolvent is the polynomial of the three pairings).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.resolvent_split_pair_values`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.resolvent_split_pair_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three pairing values are computed from the actual four roots in any splitting presentation. Vieta coefficients give the resolvent, which simplifies to a translated pure cubic.

**Theorem 1.3 (The actual quartic is irreducible modulo five at every level).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.native_quartic_mod5_irreducible`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.native_quartic_mod5_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both possible signed mod-five quartics are irreducible. The positive sign uses a short Bezout certificate against the finite-field polynomial containing every irreducible factor of degree at most two. The negative sign follows by changing the sign of the variable.

**Theorem 1.4 (The projective splitting field contains a marked cubic subfield).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.native_quartic_cubic_subfield`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.native_quartic_cubic_subfield` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual pairing value in the splitting field, shifted by twice the block and divided by minus four, is a cube root of three times the square of the block. The marked element generates a cubic field by the Eisenstein criterion at three.

**Theorem 1.5 (The actual projective splitting degree is divisible by twelve).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.native_projective_degree_multiple_twelve`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.native_projective_degree_multiple_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The splitting field contains both the marked cubic subfield and a degree-four quartic root field. Their coprime degrees divide the projective splitting degree. This endpoint does not identify the full Galois image or the independence of a compositum.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.native_projective_degree_multiple_twelve`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.native_quartic_cubic_subfield`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.native_quartic_mod5_irreducible`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.resolvent_split_pair_values`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeThreeDivision.three_torsion_abscissa_iff`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic](GoldenCubicNativeElliptic.md)
