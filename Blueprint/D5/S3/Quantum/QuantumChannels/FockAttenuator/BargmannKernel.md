# Actual Hilbert sections of the completed kernel

## Abstract

Actual Hilbert sections of the completed kernel.

**Theorem 1.1 (Actual Hilbert sections of the completed kernel).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BargmannKernel.kernel_eq_transform_discarded_section`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BargmannKernel.kernel_eq_transform_discarded_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-mode carrier is lp(Natural -> H,2), with H=lp(Natural -> Complex,2). Each evaluation section is constructed as an actual H vector by continuous coordinate functionals or an absolutely convergent H-valued contraction. The kernel is the Bargmann transform of that genuine section.

The kernel agrees with the inner product against the actual two-mode exponential vector, with the conjugation convention explicit. Its absolute value is bounded by norm(V)*exp((norm(z)^2+norm(w)^2)/2). Both scalar-variable sections are entire, and the transform is injective on the completed two-mode carrier.

The discarded and retained contractions obey the corresponding one-variable exponential norm bounds. Tensor inputs give the product of their actual Bargmann transforms. These joins are used to reconstruct finite-rank Hilbert factors from arbitrary entire separated factors; arbitrary entire functions are not assumed to be in the Bargmann image.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BargmannKernel.kernel_eq_transform_discarded_section`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann](Bargmann.md)
