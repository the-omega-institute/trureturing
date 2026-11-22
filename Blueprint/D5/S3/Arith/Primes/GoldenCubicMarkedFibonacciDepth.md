# Marked golden cubic roots and Fibonacci depth

## Abstract

A single marked root of a later golden Lucas cubic reads the earlier native Fibonacci prime-power depth.

**Theorem 1.1 (Every marked residue reads the Fibonacci entry depth).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicMarkedFibonacciDepth.fibonacci_marked_residue`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicMarkedFibonacciDepth.fibonacci_marked_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a prime greater than three dividing the block L_(3^i)^2 + 3, with i positive, and use the actual Lucas parameter x = L_(3^j) for any j greater than i. Modulo every positive power of p, the cubic T^3 - 3(x^2 + 3)T + 2(x^2 + 3)x has exactly one root above each marked seed 0, 3, and -3 modulo p.

The marked root equals its seed modulo that entire power of p if and only if the same power divides F_(6 times 3^i). The proof uses classical finite simple-root Hensel lifting, unit divided differences, the existing golden cubic recurrence, and the Fibonacci doubling and tripling identities. The result is the link from marked cubic residues to the native Fibonacci depth, not a new Hensel theorem or Fibonacci rank law. The earlier block and Fibonacci entry valuation equality is already present in GoldenCubicBlockRanks.cubic_block_b_prime_rank.

The theorem is uniform in finite precision and retains the earlier same-prime divisor hypothesis. It does not assert an identification with F_(p-1), rule out depth two, settle Wall-Sun-Sun, or invoke GRH.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicMarkedFibonacciDepth.fibonacci_marked_residue`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
