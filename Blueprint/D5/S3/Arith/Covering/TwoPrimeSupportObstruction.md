# Two-Prime Support Obstruction

## Abstract

A whole distinct odd cover cannot have a common modulus supported on only two odd primes.

**Theorem 1.1 (Two-prime-supported common moduli are impossible).**

Lean statement: `D5/S3/Arith/Covering/TwoPrimeSupportObstruction.no_two_odd_prime_supported_common_modulus`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/TwoPrimeSupportObstruction.no_two_odd_prime_supported_common_modulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a distinct odd covering system whose common modulus is p^A * q^B for distinct odd primes p and q. Map each original modulus to its finite residue class and use injectivity to retain the corresponding residue label.

The existing two-odd-prime uncovered-density theorem then supplies an uncovered residue, contradicting the whole-cover property. This only excludes the two-prime-support branch.

## References

- Truth anchor: `D5/S3/Arith/Covering/TwoPrimeSupportObstruction.no_two_odd_prime_supported_common_modulus`
- Dependency: [D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity](../Congruence/TwoOddPrimeUncoveredDensity.md)
