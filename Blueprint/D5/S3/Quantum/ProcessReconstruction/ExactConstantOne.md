# Sharp Local-Output Unitary Reconstruction

## Abstract

The sum of complete single-output diamond errors bounds the global diamond distance with optimal coefficient one.

**Theorem 1.1 (The global diamond distance is bounded by the sum of local distances).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/ExactConstantOne.diamond_le_sum_localError`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/ExactConstantOne.diamond_le_sum_localError` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Commentary.*

For square unitary channels on a finite tensor product of nonzero local spaces, each observed channel retains one output and accepts the entire global input. The bound holds for unhalved diamond distance with arbitrary finite references. A complementary partial SWAP and a localized reflection handle a dominant local error. An angular estimate along the SWAP chain handles uniformly small errors.

**Theorem 1.2 (A single qubit attains equality).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/ExactConstantOne.sharp_one_site`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/ExactConstantOne.sharp_one_site` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Commentary.*

On one qubit there are two conjugation channels whose global distance and complete local distance both equal two. This attains the universal coefficient.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/ExactConstantOne.diamond_le_sum_localError`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/ExactConstantOne.sharp_one_site`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/DominantReflection](DominantReflection.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/RobustDiamond](RobustDiamond.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry](SpectrumGeometry.md)
