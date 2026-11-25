# Fixed-charge coefficients

## Abstract

Native occupations of four inverse lowerings

**Theorem 1.1 (Physical coefficient of four lowering words).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.physical_marked_compact_lowering`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.physical_marked_compact_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit Gram determinant and a word of distinct marked occurrences, use A or B in its radial disk or the true D lip at a real chart argument strictly between zero and one. The fixed-charge marked coefficient is the charge exponential times the product of the signed lifted scales and the compact affine readout of the four tagged puncture lowering words. Reflect the finite creator sum to match the inverse jet rows and recombine each puncture's corrections with the surviving creators.

**Theorem 1.2 (Affine coefficient on the occupied support).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.affineCoefficient_fourSupport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.affineCoefficient_fourSupport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each chart and four occupations, the affine coefficient in any common finite support containing the four occupied supports equals the coefficient on their union. Embed the exponent independently in each tagged slot. The extended exponent has the same covariance and charge-linear mean on the occupied slots, including at the true D lip.

**Theorem 1.3 (Native readout of four oscillator polynomials).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.compact_readout_eq_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.compact_readout_eq_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the four oscillator polynomials have all their variables in a common finite support. Multiply their tagged images in native slot order and evaluate the compact affine readout with the chart determinant and charge nome power. The result is the sum over the four polynomials' occupied monomials of the products of their coefficients and factorial Fock weights times the literal native fixed-charge term at each occupation.

**Theorem 1.4 (Native coefficient of the actual inverse lowerings).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.lowered_charge_eq_native_occupations`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.lowered_charge_eq_native_occupations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a real chart argument strictly between zero and one and the upper choice in chart D. For a charge of nonnegative energy and a finite support containing the variables of all four finite inverse lowerings, the normalized lowerings give their literal native occupation sum multiplied by the signed lifted scales and the cube of one minus the chart parameter.

**Theorem 1.5 (Independence of the ambient lowering support).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.loweredChargeTerm_support_independent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.loweredChargeTerm_support_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any chart, argument and charge, take two finite sets containing the variables of all four actual inverse lowerings. They give the same normalized fixed-charge coefficient. The two evaluations agree term by term with the readout on the four individual occupations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.affineCoefficient_fourSupport`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.compact_readout_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.loweredChargeTerm_support_independent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.lowered_charge_eq_native_occupations`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering.physical_marked_compact_lowering`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation](OriginalFourMAssignedOccupation.md)
