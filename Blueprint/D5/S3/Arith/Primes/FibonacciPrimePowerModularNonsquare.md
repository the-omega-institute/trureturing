# Prime-Power Fibonacci Quotients in Twenty-Eight Residue Classes

## Abstract

Modular Fibonacci periods exclude square quotients in twenty-eight prime residue classes.

**Theorem 1.1 (Nonsquare successive prime-power quotients).**

Lean statement: `D5/S3/Arith/Primes/FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a prime at least seven whose residue modulo 120 is none of 1, 49, 71, and 119. At every nonnegative exponent k, the positive integer quotient of F_(q^(k+1)) by F_(q^k) is not a square.

The Fibonacci recurrence gives periodic values modulo eight, three, and five. Prime-power indices reduce to four phases modulo 120. A finite residue calculation shows that in each allowed class and phase, the quotient has a nonsquare residue in at least one modulus.

The four excluded residue classes and the general Fibonacci square-class rigidity remain outside this theorem.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare`
