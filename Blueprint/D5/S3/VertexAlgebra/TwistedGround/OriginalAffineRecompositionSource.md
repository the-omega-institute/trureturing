# Complete original corrected Gaussian Laurent row

## Abstract

Complete original corrected Gaussian Laurent row

These are finite algebraic identities on the original lattice oscillator carrier. No positivity, analytic convergence, frequency cutoff or charge truncation is assumed. The determinant-unit hypothesis is retained exactly where the original normal and corrected operators require it.

**Theorem 1.1 (recompositionAmplitude_eq).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource.recompositionAmplitude_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource.recompositionAmplitude_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary finite labels and all three occupations, the finite residual contraction equals the source factorial times the ordinary affine coefficient of correctedMatrix and correctedMean.

**Theorem 1.2 (original_corrected_gaussian_row).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource.original_corrected_gaussian_row`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource.original_corrected_gaussian_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every lattice data D with IsUnit(D.G.det), arbitrary charge a, all original occupations alpha, beta and gamma, and every integer e, wick of monomial(gamma,1) against oscillatorCorrected(D,hu,a,e,monomial(alpha,1),monomial(beta,1)) equals weight(alpha) weight(beta) weight(gamma) times the affine Laurent coefficient of correctedMatrix and correctedMean on exactly the support union at e+chargeNorm(a). The empty union is included; no extra support, recurrence or recomposition equation is a premise.

The proof homogenizes both affine kernels, derives the exact auxiliary Z Y factor by native Gaussian insertion and induction, and applies ElementaryGaussianContraction.coefficient_contraction with its proved support bounds. Shared auxiliary factorial cancellation precedes bounded finite-sum reindexing. Explicit embeddings transport the effective kernel back to the original corrected kernel. The auxiliary factorization identifies the shared contraction with the corrected source/source block and source mean.

Attribution: finite Gaussian/Wick calculus and factorial Fock normalization are classical. The lattice and twisted-current suppliers retain their FLM, Dong--Nagatomo and Bakalov--Kac attributions. The exact composition on the original repository carrier is repo-derived; no external novelty is asserted. The bibliographic background does not supply an uninspected theorem or replace these proofs.

The downstream original identityK and two-row sewing remain open, with all four external factorials, both chargeScalar factors, one left average and the original inverse -Ginv/(k+1). These row identities do not establish VOA or Jacobi axioms, crossing, Monster, CFT, BRST, string dynamics or a physical realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource.original_corrected_gaussian_row`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalAffineRecompositionSource.recompositionAmplitude_eq`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectedRowRecompositionSource](OriginalCorrectedRowRecompositionSource.md)
