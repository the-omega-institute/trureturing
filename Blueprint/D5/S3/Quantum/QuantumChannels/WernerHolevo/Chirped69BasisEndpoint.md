# Symmetric Werner–Holevo rank in dimension 69

## Abstract

The symmetric Werner–Holevo channel in dimension 69 has mixed-unitary rank 2415.

**Theorem 1.1 (A zero gives a full symmetric unitary basis in order 69).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint.hasBasis_of_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint.hasBasis_of_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

The four seed orbits have lengths 22, 11, 1 and 1. The recorded correlations and finite pair-coverage check give orthogonality of all 35 shifted seeds. The imaginary part of the one midpoint self-correlation vanishes by the orbit involution. The 69 modulations of each shifted seed give 2415 orthogonal symmetric unitaries, the dimension of the full complex symmetric matrix space.

**Theorem 1.2 (The minimum mixed-unitary decomposition length is 2415).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint.mixedUnitaryRank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint.mixedUnitaryRank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

The certified zero of the 63 real equations supplies the basis for the channel X ↦ (tr(X)I + Xᵀ)/70. Girard et al., Theorem 19(1), gives the rank criterion. The basis yields an equal-weight decomposition, and the Choi rank gives the matching lower bound for every finite decomposition into unitary conjugations.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint.hasBasis_of_zero`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint.mixedUnitaryRank`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69ActualSeedBounds](Chirped69ActualSeedBounds.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint](ChirpedBasisEndpoint.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing](TransversalNineGluing.md)
