# Complete Fibonacci Square Classes

## Abstract

Dynamic Lucas moduli and strong Fibonacci divisibility classify every positive Fibonacci square class.

**Theorem 1.1 (All positive index pairs, with every exceptional index).**

Lean statement: `D5/S3/Arith/Primes/FibSquareclassRigidity.fibonacci_squareclass_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibSquareclassRigidity.fibonacci_squareclass_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive indices m and n, the product F_m F_n is a square exactly when the indices agree, both belong to {1, 2, 12}, or both belong to {3, 6}. Thus every other positive Fibonacci index has a singleton square class.

For an odd multiplier t greater than one, the proof separates the base index's power of three and the multiplier shift's power of two. A Lucas trace at the resulting even index is positive and is three modulo four. Trace and norm give an antiperiod of the golden unit modulo that trace. The Fibonacci product reduces to minus a square, and an actual gcd calculation establishes coprimality with the modulus. Its Jacobi symbol is minus one.

For an even multiplier with base index greater than two, Fibonacci doubling separates the Fibonacci and Lucas factors. Their discriminant identity excludes every common odd prime. A square product therefore forces the Lucas factor to be a square or twice a square. Cohn's complete Lucas classifications leave only finitely many index products; their exact Fibonacci values leave the pair {3, 6}.

For arbitrary indices, strong Fibonacci divisibility identifies the gcd of their values with F_gcd(m,n). The resulting coprime quotients are squares, so each index can be compared with the common gcd index. Common gcd indices one and two are settled by the full single-index square classification. The complete multiple-index exclusions give precisely the stated exceptional classes. This is the classical classification recorded in FFF, statement (3.4), with the same positive-index conclusion.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibSquareclassRigidity.fibonacci_squareclass_pairs`
- Dependency: [D5/S3/Arith/Primes/FibonacciOddIndexNonsquare](FibonacciOddIndexNonsquare.md)
- Dependency: [D5/S3/Arith/Primes/LucasSquareClassification](LucasSquareClassification.md)
