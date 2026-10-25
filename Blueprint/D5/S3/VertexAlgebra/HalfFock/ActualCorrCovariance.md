# Original Corr Covariance

## Abstract

Original finite correction covariance and coefficient conservation

The setting is the original ordinary oscillator algebra over Complex for arbitrary LatticeData, including rank zero, arbitrary signed charge, indefinite or degenerate symmetric even Gram form, empty support and repeated generators. The extra variable u=X none has weight one and the original oscillator weight of (i,r) is r+1. No determinant-unit, positivity or energy hypothesis is added.

The normal reflection fixes u and sends X(i,r) to the finite sum for 0<=s<=r of (-1)^(r+1)*choose(r+1,s+1)*u^(r-s)*X(i,s). The affine reflection adds (-1)^(r+1)*bilinear(D,unitCharge(i),q)*u^(r+1). For homogeneous weight R, s+weight(m)=R gives the signed exponent identity -(e+2*s)-2*N-4*weight(m)+2*t=-e-2*N-4*R+2*(s+t), for arbitrary integers e and N. On the affine side the original correction shift reads (-e-2*N-4*R+2*t)+2*s. Thus the scalar law uses the same physical coefficient index after setting N=chargeNorm D q; no nonnegative norm is inferred.

The identification of affine coefficients with (-1)^R*delta_q^t(p)/t! remains a separate source-L1 dependency. Ground symmetry, Wick and charged adjointness, full corrected-field inversion, Jacobi, fusion and the full Monster/VOA/string/AdS-CFT program are not established here. The classical twisted-lattice coordinate-change background is FLM; the native original-map assembly and its finite scalar consumer are the present library work.

The escape audit of these three public results and the three exposed original helpers is unfinished under CLAUDE 3.9: https://github.com/the-omega-institute/trureturing/issues/21172. The Reg mirror reconstructs the full source laws, but does not assert completed variation, sensitivity, observational dependence or declared_validated bindings.

**Theorem 1.1 (Covariance of the original correction map).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance.correctionPolynomial_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance.correctionPolynomial_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every original LatticeData D, charge q and oscillator polynomial p, normalReflection D (Cbar D q p) equals corrLift D q (affineSource D q p). Cbar is exactly optionEquivLeft.symm composed with the original correctionPolynomial. corrLift is constructed with the original shiftCoefficients and Finsupp.lsum and is Complex-linear and linear over the finite shift polynomial algebra; no multiplicativity is asserted. Original correctionLift_X_mul supplies the repeated-generator insertion recurrence. The singleton computation reuses half_binomial_transform and the pair computation reuses pairScalar_reflection. No reflectedWord endpoint or equivariance premise occurs.

**Theorem 1.2 (Exact original correction coefficient weight).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance.Corr_coefficient_bidegree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance.Corr_coefficient_bidegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For any sourceWeight-homogeneous original oscillator polynomial p of natural weight R, every nonzero coefficient at exponent m in Corr D q p s satisfies s+Finsupp.weight(sourceWeight D,m)=R. The proof uses the exact original matching recurrence, labelledRemainders_size and wordWeight_occurrences, followed by optionEquivLeft coefficient identification. Zero polynomials and degenerate fibres are included; no finite-dimensional total weight-space assumption occurs.

**Theorem 1.3 (Finite scalar exchange for every original source).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance.Corr_reflection_readout`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance.Corr_reflection_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every p and every family ell:Nat -> Module.Dual Complex (Oscillator D), the finite sum over s in (Corr D q p).support and t in the support of E(normalReflection(embed(Corr D q p s))) of ell(s+t) applied to its t coefficient equals the finite sum over t in the support of E(affineSource D q p) and s in the support of Corr applied to that t coefficient of ell(t+s)(Corr(... ) s). Here E is the actual optionEquivLeft. This consumes original-map covariance and performs the actual shift readout on finite polynomial supports; ell has no covariance or transpose premise.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance.Corr_coefficient_bidegree`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance.Corr_reflection_readout`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance.correctionPolynomial_reflection`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentCorrection](../LatticeHalfFockCurrentCorrection.md)
