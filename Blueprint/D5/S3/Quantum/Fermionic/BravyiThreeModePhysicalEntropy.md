# Physical output entropy on the three-mode normal form

## Abstract

Physical output entropy of the three-mode Bravyi channel on its normal form.

The input is the rank-one projector of a normalized real chiral spinor. The channel is a trace-preserving sum of Clifford conjugations with nonnegative weights throughout the closed attenuation interval.

**Theorem 1.1 (The complete output spectrum).**

Lean statement: `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.normalOutput_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.normalOutput_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The physical output is complex Hermitian. Under the signed basis change its characteristic polynomial factors into that of the real chiral block and those of the two complementary blocks. Its roots give the multiset of all eight eigenvalues with their algebraic multiplicities.

**Theorem 1.2 (The physical entropy as a block sum).**

Lean statement: `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.normalOutput_entropy_eq_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.normalOutput_entropy_eq_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the von Neumann spectral entropy formula to the density state. The complementary entropy is counted twice, and every zero eigenvalue contributes zero.

**Theorem 1.3 (Entropy order for the real Bravyi blocks).**

Lean statement: `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.bravyi_three_mode_entropy_ge_comparator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.bravyi_three_mode_entropy_ge_comparator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The comparator determinant formulas give strict positivity at every positive shift, including at the endpoints of the attenuation interval. The determinant differences also give equal traces on the two sides of each comparison. Applying the shifted-product theorem to the two block spectra counts the complementary block twice.

**Theorem 1.4 (The physical comparator has minimum entropy).**

Lean statement: `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.comparator_entropy_le_normalOutput`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.comparator_entropy_le_normalOutput` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real unit normal-form spinor and every attenuation from zero through one, the output entropy is at least the output entropy at the comparator spinor. Its first and third amplitudes are the positive square root of one half and its second amplitude is zero. The shifted determinant ordering bounds the chiral and complementary entropy contributions separately. The spectrum formula then adds the complementary contribution twice.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.bravyi_three_mode_entropy_ge_comparator`
- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.comparator_entropy_le_normalOutput`
- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.normalOutput_entropy_eq_blocks`
- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy.normalOutput_spectrum`
- Dependency: [D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks](BravyiThreeModeCARBlocks.md)
- Dependency: [D5/S3/Quantum/Fermionic/FiniteSpectrumShiftedLogEntropy](FiniteSpectrumShiftedLogEntropy.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
