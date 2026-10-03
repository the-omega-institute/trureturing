# Prime-Power Fibonacci Quotients in Two Further Residue Classes

## Abstract

A Fibonacci period modulo thirty-one excludes square quotients in two further prime classes.

**Theorem 1.1 (Alternating nonsquare residues of prime-power quotients).**

Lean statement: `D5/S3/Arith/Primes/FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a prime at least seven with residue 49 or 71 modulo 120. For every nonnegative k, the quotient of F_(q^(k+1)) by F_(q^k) is a positive integer. Its residue modulo 31 is 27 when k is even and 23 when k is odd, so it is not a square.

The Fibonacci pair has period 30 modulo 31. In the stated classes, q has order two modulo 30, so the Fibonacci values at successive powers of q alternate between 1 and 27 modulo 31. Fibonacci divisibility then gives the quotient residues; neither 27 nor 23 is a square modulo 31.

The classes 1 and 119 modulo 120 and the unrestricted prime-power square-class statement remain outside this theorem.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare`
