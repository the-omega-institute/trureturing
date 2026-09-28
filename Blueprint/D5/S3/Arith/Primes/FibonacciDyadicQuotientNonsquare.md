# Dyadic Fibonacci Quotients from k = 1

## Abstract

Dyadic Fibonacci quotients from k = 1 have nonsquare residues modulo five.

**Theorem 1.1 (Nonsquare quotients for k at least one).**

Lean statement: `D5/S3/Arith/Primes/FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least one, the integer quotient of F_(2^(k+1)) by F_(2^k) is 3 modulo five when k is one, and 2 modulo five at every later layer. Hence none of these quotients is a square. Fibonacci-Lucas doubling identifies each quotient with L_(2^k); Lucas doubling makes residue two a fixed point along the later powers of two.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare`
