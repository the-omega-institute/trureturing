# Signed orders for the Lucas residue clock

## Abstract

Signed power returns are governed by the order in the unit group modulo its two global signs.

**Theorem 1.1 (All signed return lags).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_dvd_iff_modEq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_dvd_iff_modEq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The powers of a unit that return to either plus one or minus one modulo the full modulus occur exactly at multiples of its order in the quotient by the subgroup of the two global signs.

**Theorem 1.2 (Least positive signed return).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_isLeast`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive modulus the signed order is positive and is the least positive exponent returning to one of the two signs. Modulus one has order one.

**Theorem 1.3 (Signed periods for powers of five).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_three_mod_five_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_three_mod_five_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At modulus 5^r, the signed order of three is one when r is zero, and twice 5^(r-1) when r is positive. At odd prime powers the signs are all square roots of one, allowing use of the exact order of nine.

**Theorem 1.4 (A composite modulus distinguishes local and global signs).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicSignedOrder.mixed_sign_mod91`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicSignedOrder.mixed_sign_mod91` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At modulus 91, the third power of three is neither global sign even though its square is one. This rules out replacing the signed return by an unrestricted square condition for composite moduli.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicSignedOrder.mixed_sign_mod91`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_dvd_iff_modEq`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_isLeast`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicSignedOrder.signedOrder_three_mod_five_pow`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed](GoldenCubicBlockTailPeriodClosed.md)
