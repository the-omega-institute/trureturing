# Normal reflection readout

## Abstract

Original normal transpose in finite polynomial coordinates

The source algebra, actual tensor module and original bilinear actualForm are unchanged. D is arbitrary LatticeData; the scalar transpose uses hu:IsUnit(D.G.det), arbitrary signed charge norm and coefficient index e, and arbitrary actual tensors x,y. There is no ground symmetry, positivity, finite-dimensional full weight space or representability hypothesis. This is the classical bilinear coordinate-change setting of FLM, with no literature novelty claim.

normalP is optionEquivLeft composed with the original normalReflection and embed from ActualCorrCovariance. affineP is the same polynomial-coordinate conversion of its affineSource; it is not corrLift. The dependent JetTuple expansion retains repeated source occurrences. The proof uses the original actual_polynomial_monomial_transpose and identifies its exponent as shiftIndex(D,a,R,j)-e, with shiftIndex=-2*chargeNorm(D,a)-4*R+2*j. Linear extension through the existing monomial basis then handles every homogeneous polynomial, including zero.

The faithful four-slot escape audit is unfinished under CLAUDE 3.9: https://github.com/the-omega-institute/trureturing/issues/21332. Reg mirrors reconstruct the full source laws, but complete enrolled-template realization, variation, sensitivity, observational dependence and current selector binding are not claimed.

**Theorem 1.1 (Signed triangular generator coordinates).**

Lean statement: `D5/S3/VertexAlgebra/CorrectedInversion/NormalReadout.normalP_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CorrectedInversion/NormalReadout.normalP_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For i=(b,r), normalP(X i) is the sum for s:Fin(r+1) of the degree r-s monomial with coefficient (-1)^(r+1)*choose(r+1,s+1) times X(b,s). This coordinate helper is consumed by the dependent word-product expansion and the signed native-flow identification.

**Theorem 1.2 (Original homogeneous normal scalar transpose).**

Lean statement: `D5/S3/VertexAlgebra/CorrectedInversion/NormalReadout.normal_homogeneous_readout`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CorrectedInversion/NormalReadout.normal_homogeneous_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For sourceWeight-homogeneous p of weight R, the original left polynomialField coefficient paired with y equals paritySign(chargeNorm(a)/2) times ActualCorrCovariance.scalarReadout of normalP(p), using the original right form orientation and coefficient shiftIndex(D,a,R,j)-e in readout j. The finite dependent product identity normalP_word lies on the proof path. No desired normal covariance is assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CorrectedInversion/NormalReadout.normalP_X`
- Truth anchor: `D5/S3/VertexAlgebra/CorrectedInversion/NormalReadout.normal_homogeneous_readout`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance](../HalfFock/ActualCorrCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose](../HalfFock/NormalScalarTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](../LatticeHalfFockOriginalTranslation.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint](../TwistedGround/ActualChargedAdjoint.md)
