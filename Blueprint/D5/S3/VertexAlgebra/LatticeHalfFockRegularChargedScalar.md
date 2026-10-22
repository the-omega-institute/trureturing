# Original Charged Scalar

## Abstract

Original charged exponential under the formal two-sheet substitution

D is the unrestricted original lattice datum; a,b are arbitrary integral charges. A is the literal chargeNorm(D,a), and g is the signed original bilinear(D,a,b). G is the existing chargedEnergyGaussian, defined from the original singleton and pair logarithm. The preceding retained-source theorem identifies its coefficients with actualEnergyScalar. No positivity or rank assumption is introduced, and scalar evaluation is not a vacuum expectation.

**Theorem 1.1 (Actual Exponential Scalar).**

$$\forall D\in \operatorname{LatticeData}\left(\right), \forall a,b\in \operatorname{Charge}\left(D\right), \operatorname{sheetSubstitution}\left(\operatorname{chargedEnergyGaussian}\left(D, a, b\right)\right)=\operatorname{regularScalarOnSheet}\left(D, a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockRegularChargedScalar.actual_charged_scalar_two_sheet` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

G(T(u))=(1-u)^(A+2g)(1+u)^(-A), with both integer powers interpreted by the literal Mathlib binomial series. The proof derives the logarithmic differential law from the actual original energy coefficients, composes with the proved formal coordinate and original root, and identifies the two exponential solutions using the genuine initial coefficient one. It does not assume the desired regular scalar identity or recurrence. The full normal-polynomial Lambda/J comparison, product recurrence, and both unchanged plus/minus all-j endpoints on arbitrary original target tensors remain open. The moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT goal remains active/open.

**Theorem 1.2 (Original Regular Scalar Ratio).**

$$\forall D\in \operatorname{LatticeData}\left(\right), \forall a,b\in \operatorname{Charge}\left(D\right), \operatorname{mul}\left(\operatorname{C}\left(\operatorname{mul}\left(\operatorname{mul}\left(\operatorname{chargeScalar}\left(D, a\right), \operatorname{chargeScalar}\left(D, b\right)\right), \operatorname{epsilon}\left(D, a, b\right)\right)\right), \operatorname{eval}\left(\operatorname{clearedPolynomial}\left(\operatorname{bilinear}\left(D, a, b\right)\right), \operatorname{halfRoot}\left(\right)\right)\right)=\operatorname{mul}\left(\operatorname{mul}\left(\operatorname{mul}\left(\operatorname{C}\left(\operatorname{mul}\left(\operatorname{chargeScalar}\left(D, \operatorname{add}\left(a, b\right)\right), \operatorname{epsilon}\left(D, a, b\right)\right)\right), \operatorname{pow}\left(X, \operatorname{toNat}\left(\operatorname{add}\left(\operatorname{natAbs}\left(\operatorname{bilinear}\left(D, a, b\right)\right), \operatorname{bilinear}\left(D, a, b\right)\right)\right)\right)\right), \operatorname{chargedEnergyGaussian}\left(D, a, b\right)\right), \operatorname{halfLabel}\left(\operatorname{sub}\left(\operatorname{chargeNorm}\left(D, a\right), \operatorname{mul}\left(2, \operatorname{natAbs}\left(\operatorname{bilinear}\left(D, a, b\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockRegularChargedScalar.actual_regular_charged_scalar_ratio` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Let N=natAbs(g), r=(N+g).toNat, q=(1+t)^(-1/2), and E=A-2N. The theorem identifies chargeScalar(a) chargeScalar(b) epsilon(a,b) P_g(q) with chargeScalar(a+b) epsilon(a,b) t^r G(t) (1+t)^(E/2). Here eval(P,q) is exactly Polynomial.eval2(C,q,P), C embeds a scalar as a constant power series, and X is the formal generator t. The displayed mul, add, sub, pow and inv have their ordinary algebraic meanings, with natAbs and toNat exactly as in Lean. P_g is the unchanged original clearedPolynomial, and the half-label coefficients remain literal choose(E/2,n). The original cocycle appears exactly once on each side. The exponential closed form is derived from its actual logarithmic coefficients; no desired normalization identity is an extra hypothesis. The formal coordinate has unit linear coefficient four, so its formal substitution inverse pulls the identity back to t. Both signs of g and arbitrary integral charges are included. No positivity, rank, finite-charge cutoff, or target-vacuum premise is introduced. The norm-addition and chargeScalar normalization helpers adapt the sealed LatticeHalfFockLiteralChargedLeading.norm_add and scalar_normalization proofs and reuse LatticeActualGeneratorLocality.bilinear_add_right from LatticeActualProductKernel. Those suppliers are inherited normalization, not new mathematical credit. The new scalar comparison does not yet prove the all-label Lambda/J normal-polynomial comparison, the actual product recurrence or either unchanged all-j endpoint. Actual kernel validation does not certify complete registration or remote admission.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockRegularChargedScalar.actual_charged_scalar_two_sheet`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockRegularChargedScalar.actual_regular_charged_scalar_ratio`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFormalTwoSheetSubstitution](LatticeHalfFockFormalTwoSheetSubstitution.md)
