# Exact group point counts for the native mod-five Frobenius probes

## Abstract

Good native reductions give uniform repeated-root and irreducible mod-five Frobenius inputs.

**Theorem 1.1 (The pair enumeration counts the actual curve group).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.card_curve_points`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.card_curve_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The good short Weierstrass model has exactly one point at infinity. Nonsingular affine points correspond bijectively to all pairs satisfying the finite-field curve equation.

**Theorem 1.2 (Every native level has a good repeated-root probe at eleven or thirty-one).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.native_repeated_root_probe`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.native_repeated_root_probe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four-state Lucas cycles give point counts 9 or 15 at eleven on odd levels and 24 or 40 at thirty-one on even levels. The trace squared is four modulo five, and neither the point count nor its complementary twist count is divisible by twenty-five.

**Theorem 1.3 (At twenty-three the trace polynomial has no root modulo five).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.native_nonsplit_probe23`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.native_nonsplit_probe23` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four relevant native Lucas residues give counts 24, 16, 24 and 32. At every level the actual good-reduction point count therefore gives a root-free quadratic over F5. No Galois-inertia theorem is asserted by this endpoint.

**Theorem 1.4 (At seventeen the whole native orbit has point count fifteen).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.native_good_probe17`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.native_good_probe17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial Lucas state four enters the two-cycle eight and nine. All three reduced models have nonzero discriminant and exactly fifteen points.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.card_curve_points`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.native_good_probe17`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.native_nonsplit_probe23`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.native_repeated_root_probe`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic](GoldenCubicNativeElliptic.md)
