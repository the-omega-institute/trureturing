# Length recurrences for raw transfer coefficients

## Abstract

Length recurrences for raw transfer coefficients

**Theorem 1.1 (From finitely many initial lengths to all lengths).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreTransferRecurrence.hardCoreRaw_fibonacci_iff_initial`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreTransferRecurrence.hardCoreRaw_fibonacci_iff_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For degree r ≤ 4, the binary bond-two raw transfer coefficient at the hard-core base and a candidate formed from two Fibonacci sequences with weights of degree at most r satisfy the same recurrence in length. Its characteristic polynomial is (X² − X − 1)^(r+1). Equality for lengths n ≥ 7 is therefore equivalent to equality on the first 2(r+1) lengths starting at seven.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreTransferRecurrence.hardCoreRaw_fibonacci_iff_initial`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity](../PeriodicMPSTwoSiteAmbiguity.md)
