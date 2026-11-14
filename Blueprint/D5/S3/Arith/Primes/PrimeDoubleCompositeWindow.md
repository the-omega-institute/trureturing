# Composite windows centered at prime doubles

## Abstract

The doubles of arbitrarily large primes have prescribed finite windows without primes.

A finite collection of nonzero integer offsets can be assigned distinct odd prime divisors. For an offset j and a fresh prime r larger than its absolute value, the congruence 2a + j = 0 modulo r has a nonzero solution a modulo r. The Chinese remainder theorem combines these solutions into a residue class coprime to the product modulus. Dirichlet's theorem then supplies arbitrarily large primes in that class. The size bound makes each prescribed divisor strictly smaller than the corresponding integer.

**Theorem 1.1 (An arbitrary window and an arbitrary lower bound).**

Lean statement: `D5/S3/Arith/Primes/PrimeDoubleCompositeWindow.exists_prime_double_composite_window`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/PrimeDoubleCompositeWindow.exists_prime_double_composite_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural numbers H and B there is a prime p greater than both B and H such that every natural number between 2p - H and 2p + H, inclusive, is not prime. Nonzero offsets use the prescribed prime divisors. The central integer 2p is divisible by 2 and exceeds 2. A finite induction constructs the residue class while retaining coprimality with its modulus; the fresh prime at each step exceeds both the old modulus and the offset magnitude. The argument invokes Mathlib's Chinese remainder construction and its Dirichlet theorem for coprime natural residue classes.

## References

- Truth anchor: `D5/S3/Arith/Primes/PrimeDoubleCompositeWindow.exists_prime_double_composite_window`
