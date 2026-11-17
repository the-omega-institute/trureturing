# Physical Sector Channel Construction

## Abstract

Actual finite quantum channels and local dilations for the sector encoding.

**Theorem 1.1 (Finite Kraus and Stinespring construction).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.channel_kraus_stinespring`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.channel_kraus_stinespring` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information*. DOI: [10.1017/9781316848142](https://doi.org/10.1017/9781316848142).

*Commentary.*

For every channel between finite matrix spaces, complete positivity makes the Choi matrix positive semidefinite. Its spectral decomposition supplies a finite Kraus family. Trace preservation forces the sum of the Kraus adjoint products to be the identity on the input.

Stacking the Kraus family gives an isometry into a finite output and environment space. Partial trace over that environment equals the original channel on every input matrix, including off-diagonal units. The construction includes empty finite types where the channel exists. The Choi and Kraus argument adapts physlib revision 6a09b2d1761a0d4430083045a247eb121d8da260 under Apache-2.0.

Finite-dimensional Schrodinger-picture application. For a channel from d-dimensional to d'-dimensional complex matrices, take the input coordinates a and output coordinates b to have cardinalities d and d'. The environment coordinate type is b times a, so its dimension is exactly d*d'. The dilation in the second conjunct has matrix coordinates ((k,p),r), where k is an environment label, p is an output label and r is an input label. Thus its tensor order is environment followed by output; the first factor is traced out.

Given the Kraus family K, the stacked isometry has coefficient V((k,p),r)=K(k)(p,r). Its adjoint product sums the Kraus adjoint products over k and equals the input identity. For every complex input matrix X, the (p,q) coefficient after the left partial trace is the sum over k, r and s of K(k)(p,r)*X(r,s)*conjugate(K(k)(q,s)). This is the (p,q) coefficient of the channel's Kraus sum. In the Lean statement, CStarMatrix.ofMatrix identifies the same ordinary input matrix with the canonical matrix C*-algebra, and its inverse recovers the ordinary output matrix.

This gives the finite-dimensional Schrodinger-picture dilation directly for rectangular channels, without deriving a classification of representations of matrix algebras from the general Stinespring theorem. The identity holds for all matrices, rather than only density operators. For positive d and d' the environment has at most d*d' dimensions because this particular construction uses exactly that many labels. The theorem also retains empty finite coordinate types whenever a channel with those types exists.

The construction does not assert that d*d' is the minimum environment dimension, identify that minimum with Choi rank, compare two minimal dilations, or extend the isometry to a joint unitary with a fixed pure environment. It also gives no reconstruction of a microscopic bath, Hamiltonian or interaction history from the reduced channel.

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
