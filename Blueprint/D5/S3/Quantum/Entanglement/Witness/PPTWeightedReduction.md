# Marginal bounds for PPT process tomography

## Abstract

Marginal-dependent bounds on the least realignment singular value of a PPT probe.

**Theorem 1.1 (The reduction inequality).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.le_alice_identity_kron_marginal_of_ppt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.le_alice_identity_kron_marginal_of_ppt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michał Horodecki and Paweł Horodecki (1999). *Reduction criterion of separability and limits for a class of protocols of entanglement distillation*. DOI: [10.1103/PhysRevA.59.4206](https://doi.org/10.1103/PhysRevA.59.4206). URL: <https://arxiv.org/abs/quant-ph/9708015v2>.

*Commentary.*

The transpose-composed reduction map is a sum of congruences by antisymmetric matrix units. Applying it to the partially transposed probe bounds the original probe above by the first identity tensored with the second marginal.

**Theorem 1.2 (The marginal controls the least detectable direction).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.weighted_converse_of_ppt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.weighted_converse_of_ppt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michał Horodecki and Paweł Horodecki (1999). *Reduction criterion of separability and limits for a class of protocols of entanglement distillation*. DOI: [10.1103/PhysRevA.59.4206](https://doi.org/10.1103/PhysRevA.59.4206). URL: <https://arxiv.org/abs/quant-ph/9708015v2>.

*Commentary.*

For an equal-dimensional probe in the eigenbasis of its positive second marginal, the upper bound on the squared least realignment singular value is the dimension minus one divided by the dimension squared times the inverse marginal trace minus one. The weighted trace bound comes from the reduction criterion. The normalized identity direction contributes the additional trace term.

**Theorem 1.3 (A zero marginal entry forces zero gain).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.leastRealignmentSV_eq_zero_of_marginal_entry_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.leastRealignmentSV_eq_zero_of_marginal_entry_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michał Horodecki and Paweł Horodecki (1999). *Reduction criterion of separability and limits for a class of protocols of entanglement distillation*. DOI: [10.1103/PhysRevA.59.4206](https://doi.org/10.1103/PhysRevA.59.4206). URL: <https://arxiv.org/abs/quant-ph/9708015v2>.

*Commentary.*

A vanishing diagonal entry of a marginal of a positive matrix forces the corresponding block row and block column of the probe to vanish. The square realignment then has a zero singular value.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.le_alice_identity_kron_marginal_of_ppt`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.leastRealignmentSV_eq_zero_of_marginal_entry_eq_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.weighted_converse_of_ppt`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound](RealignmentSchurBound.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock](../../Matrix/LinPsiMap/ReductionBlock.md)
- Dependency: [D5/S3/Quantum/Matrix/PartialTransposeTrace](../../Matrix/PartialTransposeTrace.md)
