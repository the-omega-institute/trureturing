# Entropy comparison from shifted products

## Abstract

Finite-spectrum entropy order from actual shifted determinant order.

**Theorem 1.1 (The logarithmic integral at finite cutoff).**

Lean statement: `D5/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy.integral_log_shifted_product_sub_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy.integral_log_shifted_product_sub_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two nonnegative spectra on the same finite index type and with equal sums have matching constant and linear cutoff terms. The integral of the difference of the logarithms of their shifted products is the entropy difference plus a difference of remainders.

**Theorem 1.2 (Shifted product order implies entropy order).**

Lean statement: `D5/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy.entropy_le_of_shifted_product_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy.entropy_le_of_shifted_product_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If one shifted product is larger at every positive shift, its spectrum has greater or equal entropy. The remainder for an entry x is bounded by its square divided by the cutoff. A zero entry contributes zero entropy.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy.entropy_le_of_shifted_product_le`
- Truth anchor: `D5/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy.integral_log_shifted_product_sub_eq`
