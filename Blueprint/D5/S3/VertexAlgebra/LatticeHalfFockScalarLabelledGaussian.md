# Labelled Gaussian Source Correction

## Abstract

Retained Gaussian correction of finite actual oscillator source powers

D is any finite integral symmetric even-diagonal lattice datum. The correction-polynomial result requires no inverse Gram matrix, positivity or occupation bound. The original native-field conclusion additionally uses precisely hu:IsUnit D.G.det. Its NativeLattice object pairs D with hu, retaining both parameters without extra hypotheses. A source direction is a finitely supported complex family f on Index D, and p=sum_i f_i X_i. Every frequency is the original sourceWeight(i)=i.2+1. The formal parameter z counts source factors; it is not the two-sheet coordinate t and degree n is not a fixed-energy truncation.

The supplier correctedSource is exactly optionEquivLeft.symm composed with correctionPolynomial, not a new source map. Its existing multiplication and unit proofs are used through exact private constant references without changing their source bodies. The finite matching supplier keeps occurrence lists, including repeated colours, before combining coefficients. Set P=sum_i f_i (X(some i)+singletonPolynomial(c,i)), delta=sum_i f_i pairDerivation(i), and K=sum_i sum_j f_i f_j pairPolynomial(i,j). P retains every actual oscillator variable and singleton shift; K uses the original pairScalar, with no half inserted in that supplier. All sums here run over the actual finite support of f.

For F_n=correctedSource(c,p^n), the actual insertion operation gives F_(n+1)=(P+delta)F_n. The existing singleton and pair correction laws give delta(P)=K and delta(K)=0. Induction on the actual source powers proves delta(F_(n+1))=(n+1)K F_n. Thus F_(n+2)=P F_(n+1)+(n+1)K F_n, with the true initial polynomials F_0=1 and F_1=P. The factor n+1 is derived from the insertion commutator, not imposed as a matching-count assumption. The closed formal series is E(z)=exp(Pz+Kz^2/2). Its derivative is (P+Kz)E; the coefficient recurrence and its initial coefficients identify F_n=n! [z^n]E. The sole unordered-pair factor one half occurs in Kz^2/2; the pairScalar supplier remains unchanged.

**Theorem 1.1 (Actual Native Field Of Corrected Source Powers).**

$$\operatorname{ActualSourceGaussian}\left(D, hu, c, f, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockScalarLabelledGaussian.actual_source_field_gaussian_closed` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The exact conclusion is Ytw(D,hu)(single c (p^n)) = n! times nativeCorrectionEvaluation(D,hu,c)([z^n]E). The evaluation is precisely the original finite shiftCoefficients/shiftLinear/normalPolynomial pipeline. It introduces no replacement field or carrier. This is equality of native fields, hence holds at every original mode on every actual target tensor. No infinite coefficient interchange is used in the source-power argument: finite source sums are handled by linearity, and the exponential substitution has zero constant coefficient. This is the classical finite Gaussian/Wick calculation on the actual correction operators, with no novelty claim.

This result is a finite-direction source-power bridge, not the all-energy coefficient Gaussian identity of creationCoeff(a,j). It does not prove the two-sheet coordinate composition, the native charged-product/source-field comparison, or either all-j original iterate identity. In particular the original modes -g-j-1 and g-j-1, full q_a=bilinear(a,a), g=bilinear(a,b), chargeScalar, ground cocycles, minus-charge monodromy and M-2r remain the unchanged obligations of that comparison. The existing cleared-diagonal and below-start results remain separate suppliers; no claim is made that importing them closes these gaps. The original moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT goal remains open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockScalarLabelledGaussian.actual_source_field_gaussian_closed`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockAllStateField](LatticeHalfFockAllStateField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectionTranslation](LatticeHalfFockCorrectionTranslation.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTwoSheetChartRecurrence](LatticeHalfFockOriginalTwoSheetChartRecurrence.md)
