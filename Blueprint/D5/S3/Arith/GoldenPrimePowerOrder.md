# Golden Prime-Power Order

## Abstract

A golden residue at exact prime depth has exact order at every higher precision.

**Theorem 1.1 (Exact order in the golden residue ring).**

Lean statement: `D5/S3/Arith/GoldenPrimePowerOrder.golden_prime_power_order`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenPrimePowerOrder.golden_prime_power_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and a golden residue whose two coordinates are not both divisible by p, the element 1+p^m u has order p^n modulo p^(m+n) when m is positive and m+2 is at most p*m. A return at an earlier p-power would make both coordinates vanish modulo p, while the binomial expansion gives the return at p^n.

## References

- Truth anchor: `D5/S3/Arith/GoldenPrimePowerOrder.golden_prime_power_order`
