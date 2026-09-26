# Golden Prime-Power Order

## Abstract

A golden residue at exact prime depth has exact order at every higher precision.

**Theorem 1.1 (Exact order in the golden residue ring).**

Lean statement: `D5/S3/Arith/GoldenPrimePowerOrder.golden_prime_power_order`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenPrimePowerOrder.golden_prime_power_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and a golden residue whose two coordinates are not both divisible by p, the element 1+p^m u has order p^n modulo p^(m+n) under the stated depth inequality. This supplies the prime-power lifting step used in PCL2; identifying the first Fibonacci matrix return and its original depth remains a separate obligation.

## References

- Truth anchor: `D5/S3/Arith/GoldenPrimePowerOrder.golden_prime_power_order`
