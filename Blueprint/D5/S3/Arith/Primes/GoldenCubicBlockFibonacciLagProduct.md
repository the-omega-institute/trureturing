# Fibonacci factorization of cubic Lucas block differences

## Abstract

A golden trace polarization factors differences of native cubic Lucas blocks into Fibonacci terms.

**Theorem 1.1 (Signed Lucas square difference).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct.lucas_sq_sub_signed_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct.lucas_sq_sub_signed_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For indices n at least m, the golden norm of the intervening power supplies the sign on the earlier Lucas square. Golden trace polarization factors the result into five times the Fibonacci terms at the sum and difference of the indices.

**Theorem 1.2 (Exact native cubic block lag product).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct.cubic_block_fibonacci_lag_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct.cubic_block_fibonacci_lag_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The powers of three are odd, so the sign disappears for the native cubic blocks. The identity holds over the integers before reduction at any prime or precision.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct.cubic_block_fibonacci_lag_product`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct.lucas_sq_sub_signed_sq`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
