# Finite Local SWAP Reconstruction

## Abstract

Complete single-output channel distances control the doubled unitary and determine the global conjugation when they vanish.

**Definition 1.1 (Full-input channel with one output site).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/SwapReconstruction.siteChannel`

*Formalization.* `D5/S3/Quantum/ProcessReconstruction/SwapReconstruction.siteChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each site has its own finite basis type. For site i, keep just output i after conjugation by the unitary on the entire finite tensor product. The input domain remains the entire tensor product.

**Proposition 1.2 (Operator-norm control of the doubled unitary).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/SwapReconstruction.swap_sewing_opNorm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/SwapReconstruction.swap_sewing_opNorm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hsin-Yuan Huang, Yunchao Liu, Michael Broughton, Isaac Kim, Anurag Anshu, Zeph Landau and Jarrod R. McClean (2024). *Learning Shallow Quantum Circuits*. DOI: [10.1145/3618260.3649722](https://doi.org/10.1145/3618260.3649722). URL: <https://arxiv.org/abs/2401.10095v1>.

*Acknowledgement.* Pablo Arrighi, Vincent Nesme and Reinhard F. Werner (2011). *Unitarity plus causality implies localizability*. DOI: [10.1016/j.jcss.2010.05.004](https://doi.org/10.1016/j.jcss.2010.05.004). URL: <https://arxiv.org/abs/0711.3975v3>.

*Commentary.*

For any two unitaries U and V on the same tensor product, the operator norm of the difference between U† ⊗ U and V† ⊗ V is at most the sum of the unhalved diamond distances of their single-output channels. Each distance permits an arbitrary finite reference alongside the global input.

Trace duality bounds the difference of the two conjugated local swaps site by site. Telescoping their products and multiplying by the full swap gives the doubled-unitary estimate. The conjugated SWAP construction is related to Huang et al., arXiv:2401.10095v1, Eq. (6), Remark 5 Eq. (109) and §5.2.2 Lemma 9, and to Arrighi, Nesme and Werner, arXiv:0711.3975v3, §IV Theorem 1. Lemma 9 uses Heisenberg Pauli errors. The estimate here uses complete reduced-channel norms.

**Proposition 1.3 (Exact uniqueness from all one-site output channels).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/SwapReconstruction.conjugation_eq_of_siteChannel_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/SwapReconstruction.conjugation_eq_of_siteChannel_eq` (`✓ std3`). ∎

*Citation.* Benjamin Schumacher and Reinhard F. Werner (2004). *Reversible Quantum Cellular Automata*. DOI: [10.48550/arXiv.quant-ph/0405174](https://doi.org/10.48550/arXiv.quant-ph/0405174). URL: <https://arxiv.org/abs/quant-ph/0405174v1>.

*Commentary.*

Equality of all full-input single-output channels forces equality of the global conjugation channels. The proof first makes the doubled-unitary difference vanish, then compares the coefficients of the two conjugations on every global matrix. Schumacher and Werner, quant-ph/0405174v1, §I and Lemma 2(1), give the corresponding uniqueness principle for homomorphisms specified by their local action.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/SwapReconstruction.conjugation_eq_of_siteChannel_eq`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/SwapReconstruction.siteChannel`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/SwapReconstruction.swap_sewing_opNorm_le`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels](ReconstructionChannels.md)
