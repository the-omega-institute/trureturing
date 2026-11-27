# Eisenstein tests for the monic Thue companion

## Abstract

A primary square-role norm gives one monic integral cubic with two Eisenstein certificates.

**Theorem 1.1 (Exact coefficients after translating the variable by one).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.shifted_eq_comp`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.shifted_eq_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting X+1 in the companion cubic gives quadratic coefficient 3-6P, linear coefficient 3-12P+9P^2, and constant 1-6P+9P^2-E^2P.

**Theorem 1.2 (The same companion is Eisenstein at the role prime and after shifting at three).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.primary_pair_eisenstein`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.primary_pair_eisenstein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be the primary integral coordinates, a congruent to one and b to zero modulo three, with prime norm P = a^2-ab+b^2. Put A = a^2-b^2, D = 2ab-b^2 and E = A-2D. The monic companion is X^3-6PX^2+9P^2X-E^2P. The norm identity and primality rule out P dividing E, so the companion is Eisenstein at P.

The substitution X+1 makes the constant congruent to three modulo nine. The two other nonleading coefficients are divisible by three, so the shifted companion is Eisenstein at three. The theorem is a polynomial statement, not an assertion about the maximal order, field discriminant, or conductor.

**Theorem 1.3 (Both local certificates attach to the actual native square role).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.native_role_pair_eisenstein`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.native_role_pair_eisenstein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the proposed two-prime Lucas block, the same generator of the original square ideal gives a monic degree-three polynomial that is Eisenstein at the role prime and, after translation, at three.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.native_role_pair_eisenstein`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.primary_pair_eisenstein`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueEisenstein.shifted_eq_comp`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueDescent](GoldenCubicThueDescent.md)
