# Prime Factors and Pure Prime Classes

## Abstract

Every prime divisor of a modulus in a sum-minimal distinct odd covering system occurs as a pure prime modulus, and every nonempty such system contains a pure prime class.

**Theorem 1.1 (Prime divisors occur as pure prime moduli).**

Lean statement: `D5/S3/Arith/Covering/PrimeFactorPureClass.prime_dvd_modulus_is_present`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/PrimeFactorPureClass.prime_dvd_modulus_is_present` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a distinct odd covering system with L classes, and suppose that the sum of its moduli is no larger than the sum for every distinct odd covering system with L classes. If p is prime and p divides the modulus of class i, then some class j has modulus p.

If no class had modulus p, replace the modulus of class i by p and retain its residue. The old class is contained in the new one because p divides the old modulus, while oddness, the nonunit condition, and pairwise distinctness are preserved. The new modulus is strictly smaller, contradicting minimality of the modulus sum.

**Theorem 1.2 (Nonempty covers contain a pure prime class).**

Lean statement: `D5/S3/Arith/Covering/PrimeFactorPureClass.exists_pure_prime_class`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/PrimeFactorPureClass.exists_pure_prime_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the system has at least one class, choose one of its indices. Its modulus is greater than one and therefore has a prime divisor. The preceding result supplies an index whose modulus is exactly that prime.

## References

- Truth anchor: `D5/S3/Arith/Covering/PrimeFactorPureClass.exists_pure_prime_class`
- Truth anchor: `D5/S3/Arith/Covering/PrimeFactorPureClass.prime_dvd_modulus_is_present`
