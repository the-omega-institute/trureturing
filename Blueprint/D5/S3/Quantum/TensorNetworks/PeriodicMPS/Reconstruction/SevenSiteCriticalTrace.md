# Trace recurrence and raw marginal for the seven-site chart

## Abstract

Trace recurrence and raw marginal for the seven-site chart

**Theorem 1.1 (Trace recurrence on aligned matrix pairs).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalTrace.wordTrace_eq_matrixTrace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalTrace.wordTrace_eq_matrixTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two bond matrices over a commutative ring whose traces are one and zero respectively, the recurrence using their determinants and mixed trace computes the matrix trace of any binary word. The proof reduces words in the basis formed by the identity, the two matrices, and their ordered product.

**Theorem 1.2 (Raw two-site marginal on the aligned chart).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalTrace.rawGram_eq_rawTwo`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalTrace.rawGram_eq_rawTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an aligned complex core, every entry of the split Gram with conjugated second invariants agrees with the raw two-site marginal of the seven-letter periodic trace-word amplitudes. The contraction sums over the five omitted binary sites.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalTrace.rawGram_eq_rawTwo`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalTrace.wordTrace_eq_matrixTrace`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity](../../PeriodicMPSTwoSiteAmbiguity.md)
