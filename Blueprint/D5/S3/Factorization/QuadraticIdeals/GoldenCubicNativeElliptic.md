# The native Lucas elliptic curve and exact CM contact

## Abstract

The native Lucas cubic is the actual two-division field and block depth is CM contact order.

**Theorem 1.1 (The native cubic is the full two-division field).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.native_two_division`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.native_two_division` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the group law on actual nonsingular affine points. Their nonzero two-torsion abscissas are exactly the cubic roots, and these abscissas generate the native canonical cyclic field of degree three. The short Weierstrass model has zero ordinate at every such torsion point.

**Theorem 1.2 (The whole later elliptic curve reduces to the same CM model).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.earlier_prime_good_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.earlier_prime_good_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At any prime greater than three dividing an earlier block, every later curve has good reduction and reduces to the same equation y squared equals x cubed minus nine x. This identifies the entire reduced curve, not only the splitting behavior of its two-division polynomial.

**Theorem 1.3 (The exact CM contact order recovers the earlier valuation).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.native_elliptic_cm_contact`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.native_elliptic_cm_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The j-invariant is 1728 plus the square of twenty-four times the native Lucas coordinate. After an earlier prime occurs, the later coordinate has precisely the valuation of the original block, without further increases. Therefore the j-invariant approaches 1728 to exactly twice that depth.

**Theorem 1.4 (A square block divisor is equivalent to fourth-order CM contact).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.native_wss_iff_cm_contact`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.native_wss_iff_cm_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The earlier prime is a square divisor of its block if and only if a later curve has j-invariant equal to 1728 modulo its fourth power. This is an exact reformulation of the local divisibility condition and does not exclude or exhibit such a prime.

**Theorem 1.5 (Two constant quadratic twists have explicit rational points).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.twist_points`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.twist_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native cubic evaluates to eight and minus eight at the two arguments one away from the Lucas coordinate. The resulting points on the twists by plus and minus two are certified nonsingular. Separate checked slope formulas do not assert the rank of the base curve.

**Theorem 1.6 (Two variable twists have three explicit rational points).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.variable_twist_points`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.variable_twist_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are two explicit nonsingular points on the twist by six times the nonzero Lucas coordinate, and one on the twist by minus three times that coordinate. This statement certifies the points on the actual curves but does not certify their infinite order or independence.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.earlier_prime_good_reduction`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.native_elliptic_cm_contact`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.native_two_division`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.native_wss_iff_cm_contact`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.twist_points`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic.variable_twist_points`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCyclic](GoldenCubicNativeCyclic.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeForwardSplitting](GoldenCubicNativeForwardSplitting.md)
