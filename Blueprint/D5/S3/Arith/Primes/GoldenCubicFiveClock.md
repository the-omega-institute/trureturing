# The five-adic Lucas residue clock

## Abstract

The cubic Lucas sequence has a five-adic cycle from level zero, with explicit least period at every precision.

**Theorem 1.1 (Exact valuation at every five-adic lag).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_lag`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_lag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factor of five in the native Fibonacci product contributes one digit. The two Fibonacci depths at five equal their index depths, whose sum is the depth of nine raised to the lag minus one.

**Theorem 1.2 (Five-adic collisions are signed returns from the first level).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At precision a, two distinct levels collide exactly when their lag is a multiple of the signed order of three modulo 5^(a-1), interpreting the exponent as natural subtraction.

**Theorem 1.3 (Explicit five-adic period).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_collision_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_collision_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every lag is a return through precision one. At precision a greater than one, exactly the multiples of twice 5^(a-2) are returns, including from level zero.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_collision`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_collision_explicit`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicFiveClock.cubicBlock_five_lag`
- Dependency: [D5/S3/Arith/Primes/FibonacciFiveAdicDepth](FibonacciFiveAdicDepth.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct](GoldenCubicBlockFibonacciLagProduct.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicSignedOrder](GoldenCubicSignedOrder.md)
