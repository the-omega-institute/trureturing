# Native positive-environment transport

## Abstract

Native positive-environment transport

**Theorem 1.1 (Exact gauge and positive-scalar iterate transport).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments.native_environment_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments.native_environment_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every admissible c,e, arbitrary complex rows l and r and natural N,p,q, leftTarget of l S equals normSq(u) to minus p times S dagger dualTransfer(A) iterated p on l dagger l times S. The native right target is exactly G squared times the outside congruence normSq(u) to N-q times S inverse transfer(A) iterated q on r r dagger times S inverse dagger, times G squared dagger. The scalar is written normSq(u)^N times inverse(normSq(u)^q), so N=0 is included. This follows from native_extraction and finite transfer iteration. G is never moved into the iterate.

**Theorem 1.2 (Both actual native target matrices are positive definite).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments.certificate_positive_targets`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments.certificate_positive_targets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For p,q at least one, real canonical x with positive sigma and P(p,q)(x) nonzero, and every e squared=D(coreCoordinates x), BOTH actual native leftTarget at p and rightTarget at q for the full nativeRight at N=(p+2)+q of sqrt(sigma)(1,eta) are PosDef. Jden supplies c2 nonzero; Wnorm supplies the exact nonzero determinant of the two canonical right seed columns. The original positive_iterates is exposed in place with its body unchanged and reused. Exact gauge transport, strictly positive normSq(u) scalars, invertible S and its inverse, and invertible G squared preserve PosDef. The right congruence remains outside transfer iteration.

This environment bridge is consumed by the lengthwise canonical exclusion theorem. It proves no observed-image density or full C9 conclusion. The original C8 canonical source attribution remains Ma-Zhang, CC BY 4.0.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments.certificate_positive_targets`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments.native_environment_transport`
- Dependency: [D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate](InteriorSpectralCertificate.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity](OpenBoundaryMPSInteriorGenericity.md)
