# Exact digits of native cubic Lucas factor roles

## Abstract

A square-times-cube native Lucas block forces different congruences on its two factor roles.

**Theorem 1.1 (The square-role first ternary digit alternates).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits.native_square_role_digits`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits.native_square_role_digits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native Fibonacci rank controls the denominators of both prime factors. The block's first nonzero ternary digit comes entirely from the square role.

**Theorem 1.2 (The square-role prime predecessor has exact ternary depth).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits.square_role_pred_valuation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits.square_role_pred_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime minus one is divisible by the next ternary power, but not the following one.

**Theorem 1.3 (The cube-role dyadic residue is tied to the square role).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits.cube_role_mod128_coupling`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits.cube_role_mod128_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Modulo 128 the cube-role factor is 43 times the tenth power of the square-role factor. In particular it is always 3 modulo 8, and its native prime-rank condition supplies 19 modulo 24.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits.cube_role_mod128_coupling`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits.native_square_role_digits`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits.square_role_pred_valuation`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockRanks](GoldenCubicBlockRanks.md)
