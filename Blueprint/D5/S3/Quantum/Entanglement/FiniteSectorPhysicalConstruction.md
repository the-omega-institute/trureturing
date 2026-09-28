# Physical Sector Channel Construction

## Abstract

Actual finite quantum channels and local dilations for the sector encoding.

**Theorem 1.1 (Finite Kraus and Stinespring construction).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.channel_kraus_stinespring`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.channel_kraus_stinespring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every channel between finite matrix spaces, complete positivity makes the Choi matrix positive semidefinite. Its spectral decomposition supplies a finite Kraus family. Trace preservation forces the sum of the Kraus adjoint products to be the identity on the input.

Stacking the Kraus family gives an isometry into a finite output and environment space. Partial trace over that environment equals the original channel on every input matrix, including off-diagonal units. The construction includes empty finite types where the channel exists. The Choi and Kraus argument adapts physlib revision 6a09b2d1761a0d4430083045a247eb121d8da260 under Apache-2.0.

**Theorem 1.2 (Physical encodings and residual splitter).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.physical_encoding`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.physical_encoding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive sector ranks and normalized residual spectra, the prescribed source and flat target isometries induce actual quantum channels. Arbitrary local channel pairs have an actual product channel, and finite probability mixtures have an actual shared-classical channel. Each identity holds on every physical input matrix.

The residual splitter traces out the spectral coordinate on both local systems. Its local output is the explicit partial trace on every input matrix. On encoded logical matrices, the joint channel multiplies each sector pair by the Gram overlap of the residual spectra before applying the flat target encoding.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.channel_kraus_stinespring`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.physical_encoding`
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorChannelModel](FiniteSectorChannelModel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
