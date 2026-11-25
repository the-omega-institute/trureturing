# Robust Local-Output Unitary Reconstruction

## Abstract

Dimension-independent stability in unhalved diamond distance from complete single-output unitary channel data.

Let U and V be arbitrary unitaries on a finite tensor product of nonzero local spaces. For every site i, trace out all other outputs. Both resulting channels still take the full global input. Let δ be the sum over sites of the unhalved diamond distances of these pairs, and let D be the unhalved diamond distance between the global conjugation channels. Every distance permits arbitrary finite ancillas on the input, with their identity action retained in the output.

**Lemma 1.1 (Coefficient one from a small doubled-unitary error).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_sewing_of_lt_sqrt_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_sewing_of_lt_sqrt_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Acknowledgement.* Nathaniel Johnston, David W. Kribs and Vern I. Paulsen (2009). *Computing stabilized norms for quantum operations*. DOI: [10.26421/QIC9.1-2-2](https://doi.org/10.26421/QIC9.1-2-2). URL: <https://arxiv.org/abs/0711.3636v1>.

*Commentary.*

For any finite nonzero basis and two unitaries, an operator-norm upper bound ε below √3 for the doubled-unitary difference also bounds D. A maximal spectral chord of the relative unitary gives a common spectral half-plane and hence a lower bound on every pure output overlap. The canonical pure-state reduction transfers the resulting upper bound to diamond distance.

**Proposition 1.2 (Coefficient one for small complete local-output error).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_sum_localError_of_lt_sqrt_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_sum_localError_of_lt_sqrt_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Acknowledgement.* Nathaniel Johnston, David W. Kribs and Vern I. Paulsen (2009). *Computing stabilized norms for quantum operations*. DOI: [10.26421/QIC9.1-2-2](https://doi.org/10.26421/QIC9.1-2-2). URL: <https://arxiv.org/abs/0711.3636v1>.

*Commentary.*

If δ < √3, then D ≤ δ. The operator-norm step comes from the local SWAP comparison. The √3 threshold is sufficient for the spectral half-plane argument.

**Proposition 1.3 (Global bound with the spectral conversion factor).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_min_scaled_sum_localError`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_min_scaled_sum_localError` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Acknowledgement.* Nathaniel Johnston, David W. Kribs and Vern I. Paulsen (2009). *Computing stabilized norms for quantum operations*. DOI: [10.26421/QIC9.1-2-2](https://doi.org/10.26421/QIC9.1-2-2). URL: <https://arxiv.org/abs/0711.3636v1>.

*Commentary.*

For every δ, D ≤ min(2, (2/√3)δ). Below √3 use the coefficient-one estimate. At and above √3 use the universal distance bound of two. The factor 2/√3 is used here as an upper bound for the local-error sum formulation.

**Proposition 1.4 (Clipped bound with coefficient two).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_two_min_one_sum_localError`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_two_min_one_sum_localError` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Acknowledgement.* Nathaniel Johnston, David W. Kribs and Vern I. Paulsen (2009). *Computing stabilized norms for quantum operations*. DOI: [10.26421/QIC9.1-2-2](https://doi.org/10.26421/QIC9.1-2-2). URL: <https://arxiv.org/abs/0711.3636v1>.

*Commentary.*

The same pair also obeys D ≤ 2 min(1, δ), by using the small-error result up to δ = 1 and the universal distance bound for δ ≥ 1.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_min_scaled_sum_localError`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_sewing_of_lt_sqrt_three`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_sum_localError_of_lt_sqrt_three`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/RobustDiamond.diamond_le_two_min_one_sum_localError`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/PureDistance](PureDistance.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry](SpectrumGeometry.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum](UnitarySpectrum.md)
