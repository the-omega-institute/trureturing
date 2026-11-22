# Amplified Reflection and a Dominant Site

## Abstract

A complementary partial SWAP localizes a test of orthogonal global outputs.

**Theorem 1.1 (Commutator bound after the complementary SWAP).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/DominantReflection.complement_commutator_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/DominantReflection.complement_commutator_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Commentary.*

Swapping all sites except one transports a system reflection into an amplified observable on the remaining site. The complete diamond error at that site bounds its commutator with the transported unitary.

**Theorem 1.2 (A large local error forces nonzero global overlap below total error two).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/DominantReflection.no_zero_overlap_of_dominant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/DominantReflection.no_zero_overlap_of_dominant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Commentary.*

If one site has error at least one and the total is less than two, the partial SWAP on the other sites and the rank-one reflection bound rule out a unit input vector orthogonal to its unitary image.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/DominantReflection.complement_commutator_le`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/DominantReflection.no_zero_overlap_of_dominant`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/PartialSwap](PartialSwap.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum](UnitarySpectrum.md)
