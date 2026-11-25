# Fourier construction and Gram factorization of chirped circulants

## Abstract

Fourier construction and Gram factorization of chirped circulants.

**Theorem 1.1 (Unitarity under diagonal phase multiplication).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram.chirped_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram.chirped_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

A unit-modulus spectrum gives a unitary circulant. Multiplying on both sides by the diagonal chirp and modulation phases preserves unitarity. Evenness of the spectrum supplies the separate transpose identity.

**Theorem 1.2 (Separation of the Hilbert–Schmidt pairing).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram.chirped_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram.chirped_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

The equality holds for arbitrary complex spectra and all chirp and modulation indices over a nonzero cyclic order admitting an inverse of two. The change of variables to the sum and difference of the matrix indices separates the seed pairing from the quadratic character sum.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram.chirped_gram`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram.chirped_unitary`
- Dependency: [D5/S3/Quantum/Dynamics/PolygonalFourierCouplings](../../Dynamics/PolygonalFourierCouplings.md)
