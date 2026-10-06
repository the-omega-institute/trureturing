# Height-Coded Prime Absorption

## Abstract

A sufficiently large pure prime in a distinct odd covering system can be absorbed into fresh heights of a smaller prime, producing a whole covering system with fewer classes.

**Theorem 1.1 (One source transports every surviving original class).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/PrimeAbsorption.prime_absorption`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/PrimeAbsorption.prime_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be any finite covering system with L pairwise distinct odd moduli greater than one. Suppose its least common multiple is p^H q^G M, where p and q are distinct odd primes, H and G are positive, and M is coprime to p q. If one original modulus is q and q > p^(2H+1), then there exist L' < L and a distinct odd covering system of size L'.

The first block of 2H+1 base-p digits is injected into the q roots other than the actual residue of the original pure q class. Each later block of H+1 base-p digits supplies one q digit. This constructs a single code whose depth-e congruence is equivalent to the input congruence modulo p^(H+(H+1)e).

For each output point z, one Chinese-remainder source preserves z modulo p^H M and uses the fixed code modulo q^G. An original modulus p^a q^e m has an empty inverse or one complete inverse progression. For e > 0 its exact inverse modulus is p^(H+(H+1)e) m. The enclosure of modulus p^((H+1)e+a) m contains that entire inverse, retaining the full original cofactor condition. For e = 0 the original progression is preserved.

The replacement p-height uniquely recovers a and e by division with remainder by H+1, and the part coprime to p recovers m. Thus distinct original numerical labels give distinct output labels, all odd and greater than one. Original coverage at the same source proves coverage at every output point. The pure q class has empty inverse, so the number of output classes is strictly smaller.

The output may increase the height of p and need not preserve the original period or divisor closure. This is a conditional whole-cover reduction; it does not alone exclude every distinct odd covering system.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/PrimeAbsorption.prime_absorption`
