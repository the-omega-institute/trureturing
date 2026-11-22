# Integral charge fibers and chart transformations

## Abstract

Coefficient crossing in the physical four-point charts

**Theorem 1.1 (Termwise Taylor extraction on an integral charge fiber).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_jet_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_jet_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Give each finite mark independent spatial and weight variables. Use the regular physical covariance with its same-puncture inverse lowering correction and the original physical linear mean. In both terms use the relative chart sign on the weight of each occurrence.

The sum ranges over every integral charge q reducing to the specified mod-two sector. On one polydisk, the quadratic term in the mark weights is bounded and the linear mean is bounded by a linear function of the absolute charge coordinates. The positive definite Gram form and Im τ > 0 absorb that linear growth by completing squares. A Gaussian with exponent −π Im(τ) ⟨q,q⟩/4 remains summable. Taylor extraction then commutes with the literal charge sum, with the original inverse twelfth power of the period.

**Theorem 1.2 (Wick extraction in each physical charge summand).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_marked_coefficient_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_marked_coefficient_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a list of distinct mark labels, degree one in each selected weight is the ordered mark derivative at zero. For each spatial coordinate vector the derivative is the charge-energy exponential exp(π i τ ⟨q,q⟩/2) times the native affine Wick moment of the symmetric physical covariance and charge-dependent mean with the original occurrence signs. The moment uses the occupation factorial convention of affineMoment. Taking the indicated spatial coefficients of the moments and summing with the charge and period weights gives the corresponding Taylor coefficient of the physical product.

**Theorem 1.3 (The A/D and A/B comparisons for every Taylor coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_coefficient_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_coefficient_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use a unit Gram determinant, positive definite real Gram matrix and rank 24. Take either lip, real 0 < x < 1 and w² = 1 − 1/x with ‖w‖ < 1. Pull back the physical product overlap along the spatial projection while retaining a separate variable for each weight. Repeated punctures and colours are allowed.

Write J_c(a) for any ordered Taylor coefficient of that physical product. The D coefficient is 2⁻¹² ∑_b fourierSign(D,a,b) J_A(b). The B coefficient is (periodRoot(A,x)¹²)⁻¹ 2⁻¹² ∑_b fourierSign(D,a,b) quadraticSign(D,b) J_A(b). The same normal charge majorant controls each finite row after weighting by the sector character.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_coefficient_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_jet_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick.physical_chart_marked_coefficient_hasSum`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct](OriginalFourMPhysicalProduct.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor](OriginalFourMSpatialTaylor.md)
