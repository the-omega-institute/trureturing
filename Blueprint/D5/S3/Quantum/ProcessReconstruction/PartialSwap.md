# Partial SWAP estimates for unitary channels

## Abstract

Partial SWAP norms track the complete error at each inserted site.

**Theorem 1.1 (Control of one partial SWAP increment).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PartialSwap.norm_partial_step`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PartialSwap.norm_partial_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Commentary.*

Conjugating by additional commuting local SWAPs preserves the operator-norm estimate for an increment. The unhalved diamond error of the complete single-output channel bounds that increment.

**Theorem 1.2 (Invariance under unitary precomposition).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PartialSwap.diamondDistance_precompose_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PartialSwap.diamondDistance_precompose_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Commentary.*

Precomposing both channels with the same input conjugation preserves the diamond distance. Its inverse conjugation transports the reference-amplified optimization in the opposite direction.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PartialSwap.diamondDistance_precompose_unitary`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PartialSwap.norm_partial_step`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/PureDistance](PureDistance.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/SwapReconstruction](SwapReconstruction.md)
