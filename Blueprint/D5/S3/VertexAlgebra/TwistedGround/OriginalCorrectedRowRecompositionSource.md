# Original charged correction support and Laurent reduction

## Abstract

Original charged correction support and Laurent reduction

These are finite algebraic identities on the original lattice oscillator carrier. No positivity, analytic convergence, frequency cutoff or charge truncation is assumed. The determinant-unit hypothesis is retained exactly where the original normal and corrected operators require it.

**Theorem 1.1 (Corr_residual_support).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.Corr_residual_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.Corr_residual_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

A nonzero residual coefficient of original Corr has support contained in the original source occupation support. Characteristic-zero differentiation and the actual Corr_partial identity prove this bound; it is not assumed.

**Definition 1.2 (sourceCovariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.sourceCovariance`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.sourceCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The source/source covariance is pairScalar(r,s) times the original Gram entry, with ordinary source frequencies r=k+1.

**Definition 1.3 (sourceMean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.sourceMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.sourceMean` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The source singleton is halfBinomial(r) times the original pairing of the unit charge with a.

**Theorem 1.4 (charged_correction_coefficients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.charged_correction_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.charged_correction_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The sum of all actual shift coefficients for one residual occupation is the source factorial times the affine coefficient of the original source/residual correction kernel.

**Theorem 1.5 (charged_correction_shift_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.charged_correction_shift_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.charged_correction_shift_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The original bidegree theorem selects exactly one possible shift s: s plus residual source weight equals source source weight. At that shift the amplitude is the same affine coefficient; every other shift is zero.

**Definition 1.6 (recompositionAmplitude).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.recompositionAmplitude`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.recompositionAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The bounded residual-occupation contraction retains the original source factorial. Its bound is source occupation degree, rather than a mode cutoff.

**Theorem 1.7 (original_corrected_row_finite_reduction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.original_corrected_row_finite_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.original_corrected_row_finite_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual corrected row is reduced to this finite amplitude at its exact Laurent weight, on precisely the union of source, input and detector supports. Both external factorials, arbitrary charge, every integer exponent and empty support are retained.

**Definition 1.8 (correctedMatrix).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.correctedMatrix`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.correctedMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Complete only the normal kernel source/source block with the original pairScalar times Gram covariance. All source/input, source/output and input/output blocks remain unchanged.

**Definition 1.9 (correctedMean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.correctedMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.correctedMean` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Complete only the source mean with the original charged singleton; both external means remain unchanged.

The correction polynomial is obtained from the actual correctionLift by specializing the shift variable to one while preserving residual indeterminates. Its insertion and partial identities give a coefficient recurrence, compared with the affine Gaussian by occupation induction. Exact bidegree selection then proves the Laurent shift relation. Support enlargement uses the existing gaussianCoefficient_enlarge theorem.

Attribution: finite Gaussian/Wick calculus and factorial Fock normalization are classical. The lattice and twisted-current suppliers retain their FLM, Dong--Nagatomo and Bakalov--Kac attributions. The exact composition on the original repository carrier is repo-derived; no external novelty is asserted. The bibliographic background does not supply an uninspected theorem or replace these proofs.

The downstream original identityK and two-row sewing remain open, with all four external factorials, both chargeScalar factors, one left average and the original inverse -Ginv/(k+1). These row identities do not establish VOA or Jacobi axioms, crossing, Monster, CFT, BRST, string dynamics or a physical realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.Corr_residual_support`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.charged_correction_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.charged_correction_shift_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.correctedMatrix`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.correctedMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.original_corrected_row_finite_reduction`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.recompositionAmplitude`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.sourceCovariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource.sourceMean`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance](../HalfFock/ActualCorrCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](../LatticeHalfFockOriginalTranslation.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock](InfiniteGaussianFock.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource](OriginalNormalRowSource.md)
