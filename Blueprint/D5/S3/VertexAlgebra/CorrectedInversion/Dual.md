# Original finite dual identity

## Abstract

Finite original-source functional-dual inversion

coordinateInversion is a Complex-linear map from the original Carrier D to integer-indexed finite Carrier families. On the original monomial single(a,m), let R=weight(sourceWeight,m), N=chargeNorm(D,a) and d_j=-2N-4R+2j. Its value is the sum for j=0..R of the Finsupp singleton at d_j with vector paritySign(N/2)*(-1)^R/j! times (sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)^(-1) 1)^j applied to that original source. It is extended through the existing oscillator monomial basis and finite charge direct sum. Finsupp addition merges all coincident integer shifts and permits cancellation.

K_L is exactly the existing correctedDualCoefficient from TwistedGround.CorrectedDualCoefficient. K_R(e)(v)=actualForm(D,hu,x,Ycorr(v).coeff(e)y) keeps the distinct original right orientation. The proof uses the original integer determinant-unit assumption to identify the actual inverse-Gram Sugawara powers with SourceMobius.sectorL1 powers, consumes actual_corrected_monomial_inversion, and proves equality of linear functionals on the existing monomial/charge basis.

Only the transformed input v has finite coefficient support. The theorem makes no claim of finite charge support for a fixed dual functional, graded restricted-dual membership, representability, positivity, form symmetry or Hermitian adjointness. It does not establish the full Monster/VOA/fusion/string/AdS-CFT objective. The coordinate-change background is classical FLM, with no literature novelty claim.

The faithful four-slot escape audit is unfinished under CLAUDE 3.9: https://github.com/the-omega-institute/trureturing/issues/21332. Reg mirrors reconstruct the full source laws, but complete enrolled-template realization, variation, sensitivity, observational dependence and current selector binding are not claimed.

**Theorem 1.1 (Actual finite functional-dual identity).**

Lean statement: `D5/S3/VertexAlgebra/CorrectedInversion/Dual.actual_dual_inversion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CorrectedInversion/Dual.actual_dual_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original Carrier source v, arbitrary signed e and arbitrary actual tensors x,y under the original hu, K_L(e)(v) is the sum over d in the actual support of coordinateInversion(v) of K_R(d-e)(coordinateInversion(v)(d)). This is an actual finite coefficient sum. No injectivity of shifts, unique charge decomposition beyond the existing Finsupp, desired inversion law or representability premise is assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CorrectedInversion/Dual.actual_dual_inversion`
- Dependency: [D5/S3/VertexAlgebra/CorrectedInversion/Corrected](Corrected.md)
- Dependency: [D5/S3/VertexAlgebra/SourceMobius/OriginalCarrier](../SourceMobius/OriginalCarrier.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/CorrectedDualCoefficient](../TwistedGround/CorrectedDualCoefficient.md)
