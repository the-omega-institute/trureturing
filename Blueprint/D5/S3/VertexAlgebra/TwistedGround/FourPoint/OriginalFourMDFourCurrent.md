# The true D lip and its overlap with A

## Abstract

The original three-channel identity for four lowest-mode currents

**Theorem 1.1 (The true D-lip coefficient at fixed charge).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.chartD_four_current_fixed_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.chartD_four_current_fixed_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a lowest-mode current colour at each of P, Q, R, S, allowing repetitions. For an integral charge of nonnegative energy and real 0 < x < 1, take degree one in each mark and degree zero in the displacements of the physical D coefficient on the true lip. After division by the twelfth power of the D period, this equals −i(1−x)³/x³ times the native D-lip charge term at 1/x with occupation projection arguments (2, 2, 0, −1) in the order P, R, Q, S.

**Theorem 1.2 (The coefficient in a D-lip charge sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.chartD_four_current_sector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.chartD_four_current_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With unit Gram determinant and positive definite real Gram form, sum the fixed-charge formula over the charges in each mod-two sector. For real 0 < x < 1, the physical four-current jet equals the projection of the literal true D-lip sector at 1/x, with the same scalar, projection arguments and puncture order.

**Theorem 1.3 (Real A/D crossing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.four_current_d_lip_crossing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.four_current_d_lip_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the lattice have rank 24, positive definite real Gram form and unit Gram determinant. For arbitrary current colours, integers m, n, r with m + n + r = 2, any output charge class, and real 1/2 < x < 1, the A slit channel at 1−1/x equals the true D-lip channel at 1/x at weights (2, 2, 2). The physical A/D Fourier comparison relates the Laurent coefficients with a common nonzero scalar. Translating the quadratic Gauss sum cancels the Fourier normalization.

**Theorem 1.4 (The complex overlap of the A and D slit channels).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.four_current_slit_ad_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.four_current_slit_ad_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same lattice and signed-mode hypotheses, the canonical slit channels A and D, in their respective chart parameters, agree on a complex neighborhood of an interior point of their common chart domain for each output charge class. The analytic D-lip continuation agrees with the canonical D channel on the open lip, carrying the real equality to the overlap.

**Theorem 1.5 (The original signed-mode identity for the four currents).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.four_current_identityK`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.four_current_identityK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any valid even integral lattice of rank 24 with positive definite real Gram form and unit Gram determinant, any four lowest-mode current colours, and all signed integers m, n, r with m + n + r = 2, the original charge-coset identity K holds at weights (2, 2, 2). The A/B and A/D overlap equalities give a common germ for the residue identity. The certified Gram data for the actual Leech lattice supply the lattice hypotheses, with the colour assignment and signed modes still arbitrary.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.chartD_four_current_fixed_charge`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.chartD_four_current_sector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.four_current_d_lip_crossing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.four_current_identityK`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.four_current_slit_ad_overlap`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAFourCurrent](OriginalFourMAFourCurrent.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel](OriginalFourMDLipChannel.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussElimination](../GaussElimination.md)
