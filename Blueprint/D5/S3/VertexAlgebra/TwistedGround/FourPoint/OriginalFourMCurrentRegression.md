# The fixed-charge chart A coefficient and inverse lowering

## Abstract

The two same-puncture currents in modes one and zero

**Theorem 1.1 (The physical coefficient at fixed charge).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.chartA_same_puncture_modes_one_zero_fixed_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.chartA_same_puncture_modes_one_zero_fixed_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a lattice colour and a charge of nonnegative energy. For either lip and real 1/2 < x < 1, take degree one in each independent mark at the first A-chart puncture and displacement degrees one and zero. Normalize by the inverse twelfth power of the A period. The result is (1−t)³ divided by the square of the first puncture's scale, times the sum of three native slit charge terms. Their occupations and multipliers are one mode-one and one mode-zero current with multiplier one, two mode-zero currents with multiplier −3, and the vacuum with multiplier 3/16 of the diagonal Gram entry. The other punctures are in vacuum and the slit parameter is t = 1−1/x.

**Theorem 1.2 (Powers of oscillator lowering).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.lowering_modes_one_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.lowering_modes_one_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Gram determinant is a unit. Apply the nth power of oscillator lowering to the product of mode-one and mode-zero creation variables of the same colour, and divide by n factorial. The outputs for n = 0, 1 and 2 are the input, 3/2 times the square of the mode-zero variable, and the vacuum scaled by 3/16 times the diagonal Gram entry. All higher powers vanish.

**Theorem 1.3 (The finite factorial-weighted readout).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.chartA_same_puncture_modes_one_zero_lowering`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.chartA_same_puncture_modes_one_zero_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With unit Gram determinant and the same physical hypotheses, form the inverse lowering sum over k = 0, 1, 2, 3 with coefficient (−1)ᵏ/k! on the kth power. The normalized physical coefficient equals the sum over the resulting polynomial's support, weighting each coefficient by the occupation factorial and the fixed-charge slit term at that occupation, with the common factor (1−t)³ divided by the square of the scale. The repeated mode-zero occupation has factorial two, giving the multiplier −3.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.chartA_same_puncture_modes_one_zero_fixed_charge`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.chartA_same_puncture_modes_one_zero_lowering`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression.lowering_modes_one_zero`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAFourCurrent](OriginalFourMAFourCurrent.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCorrectionJets](OriginalFourMCorrectionJets.md)
