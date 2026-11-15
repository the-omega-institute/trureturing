# Charged correction and signed current suppliers

## Abstract

Charged correction and signed current suppliers

These are finite algebraic identities on the original lattice oscillator carrier. No positivity, analytic convergence, frequency cutoff or charge truncation is assumed. The determinant-unit hypothesis is retained exactly where the original normal and corrected operators require it.

**Definition 1.1 (affineKernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.affineKernel`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.affineKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The homogenized quadratic has blocks A, mu, transpose(mu), and zero on one auxiliary coordinate.

**Definition 1.2 (affineCoefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.affineCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.affineCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The ordinary coefficient of the finite affine Gaussian exponential is the sum of native homogeneous coefficients over auxiliary degrees zero through the occupation degree.

**Theorem 1.3 (chargedCorr_linearForms).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.chargedCorr_linearForms`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.chargedCorr_linearForms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary lattice data D, charge a, complex z, residual coordinate evaluation x, finite family c of actual oscillator linear forms and every occupation d, chargedReadout of the product equals weight(d) times the affine coefficient. The covariance is the original pairScalar times Gram times z to the sum of source frequencies. The mean retains every residual coordinate x and the charged singleton; no neutral-charge substitution is used.

**Theorem 1.4 (wick_flat_cons).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.wick_flat_cons`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.wick_flat_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The original all-signed flat-current recursion has coefficient minus (k+1) times choose(-m-1/2,k+1). A negative mode differentiates the detector; a nonnegative mode differentiates the input. Both branches retain the original doubled exponent shift.

The noncentral moment comparison uses strong induction on occupation degree after deriving the original insertion law. The auxiliary coefficient and affine-moment identities also supply the normal and corrected-row calculations.

Attribution: finite Gaussian/Wick calculus and factorial Fock normalization are classical. The lattice and twisted-current suppliers retain their FLM, Dong--Nagatomo and Bakalov--Kac attributions. The exact composition on the original repository carrier is repo-derived; no external novelty is asserted. The bibliographic background does not supply an uninspected theorem or replace these proofs.

The downstream original identityK and two-row sewing remain open, with all four external factorials, both chargeScalar factors, one left average and the original inverse -Ginv/(k+1). These row identities do not establish VOA or Jacobi axioms, crossing, Monster, CFT, BRST, string dynamics or a physical realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.affineCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.affineKernel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.chargedCorr_linearForms`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource.wick_flat_cons`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentWard](../LatticeHalfFockCurrentWard.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction](ElementaryGaussianContraction.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian](OriginalCorrectionGaussian.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset](OriginalFourMChargeCoset.md)
