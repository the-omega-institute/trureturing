# Symmetric Werner–Holevo rank in dimension 73

## Abstract

The symmetric Werner–Holevo channel in dimension 73 has mixed-unitary rank 2701.

**Theorem 1.1 (A zero gives a full symmetric unitary basis in order 73).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint.hasBasis_of_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint.hasBasis_of_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

The 36 multiplicative shifts of the chirped seed and one fixed unchirped seed give 37 seed vectors. The finite pair-coverage check and the involution at the midpoint give orthogonality from the recorded equations. Each seed has 73 modulations, giving 2701 orthogonal symmetric unitaries in a symmetric matrix space of dimension 2701.

**Theorem 1.2 (The minimum mixed-unitary decomposition length is 2701).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint.mixedUnitaryRank_seventy_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint.mixedUnitaryRank_seventy_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

The certified zero supplies the basis. Girard et al., Theorem 19(1), identifies the rank criterion. The channel sends X to (tr(X)I + Xᵀ)/74. The basis gives an equal-weight mixture, and the Choi rank gives the matching lower bound for every finite decomposition into unitary conjugations. The construction uses Ma’s Theorem 5 and Proposition 12. The conjecture for every positive dimension remains open.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint.hasBasis_of_zero`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint.mixedUnitaryRank_seventy_three`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedActualSeedBounds](ChirpedActualSeedBounds.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing](TransversalNineGluing.md)
