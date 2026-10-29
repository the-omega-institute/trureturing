# The completed balanced two-photon physical kernel

## Abstract

The completed balanced two-photon physical kernel.

**Theorem 1.1 (The completed balanced two-photon physical kernel).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedKernel.balanced_two_photon_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedKernel.balanced_two_photon_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every completed Fock input a, the existing beam splitter at transmissivity one half with the actual number-two environment has Bargmann kernel B(a)((z+w)/sqrt(2))*(w-z)^2/(2*sqrt(2)) at every complex pair. The statement uses the existing beamSplitter and tensor definitions.

The forward `beamUnitary` acts on exponential vectors by `rotate(t,r)`. When the unitary is moved through the inner product, its inverse action is `rotate(t,-r)`, so the transform is pulled back by that inverse rotation. This identifies the transform of every completed two-mode input, including arbitrary infinite support. The number-state transform is z^n/sqrt(n!), which gives the exact balanced two-photon normalization.

This is an operator-level physical bridge. It supplies neither an assigned finite matrix spectrum nor a finite-support assumption. Rescaling its two variables and its nonzero scalar preserves the exact number of separated terms, connecting the physical kernel to the quadratic weighted Hankel kernel.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedKernel.balanced_two_photon_kernel`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/BargmannKernel](BargmannKernel.md)
