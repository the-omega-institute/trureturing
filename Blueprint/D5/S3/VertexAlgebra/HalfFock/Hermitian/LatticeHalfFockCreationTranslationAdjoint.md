# Native Half-Frequency Creation and Translation Transpose

## Abstract

Native Half-Frequency Creation and Translation Transpose

The objects are the original Oscillator(D), halfCreationSeries, halfCreationExponential, halfCreationCoeff, halfTranslatedPolynomial and halfForm. The only additional coefficient selector is halfTranslationCoeff: it is zero at a negative integer degree and is the ordinary finite polynomial coefficient at a nonnegative degree. No operator is defined by assigning a desired transpose. The actual creation logarithm has coefficient 2/(2k+1); its exponential and factorials are those already proved in LatticeHalfFockChargedCoefficients. The original current has positive frequency k+1/2, so (k+1/2) times 2/(2k+1) is exactly one.

**Theorem 1.1 (Every Integer Degree and Every Polynomial Pair).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockCreationTranslationAdjoint.half_creation_translation_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockCreationTranslationAdjoint.half_creation_translation_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lattice D, integral charge a, integer degree d and original polynomials P,Q, multiplication of P by the literal halfCreationCoeff(D,a,d) is adjoint to halfTranslationCoeff(D,-a,d) acting on Q. Negative degrees are included as zero coefficients on both sides. No Gram inverse or positive signature hypothesis is needed for this algebraic identity. The original current adjoint is reused, not reproved. The proof uses the Gram-weighted original annihilation derivative of each actual creation coefficient and structural induction on the complete finite polynomial Q, generalizing both P and d. Thus the result is not restricted to monomials, the vacuum or scalar evaluation. The constant coefficient base case follows from actual odd weighted homogeneity, and the induction step uses the actual translation substitution X(i,k) minus the Gram pairing times t^(2k+1).

Proof shape: content. The new earning inference is the arbitrary finite-polynomial coefficient transpose; the consumed current adjoint, scalar normalization, constant scaling and Hermitian pullback helpers are reuse or bind-only organization, not new mathematical credit. LatticeCreationTranslationAdjoint supplies the prior integer-frequency induction architecture. LatticeHalfFockHermitian supplies the unchanged half-frequency form and current adjoints. Classical algebraic Fock geometry is the provenance; no literature novelty is claimed. The owning Reg source retains the literal theorem telescope, original readout, equivalent law, rejected variation, sensitivity and actual state dependence. Compilation and full registration admission remain distinct.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockCreationTranslationAdjoint.half_creation_translation_adjoint`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockHermitian](LatticeHalfFockHermitian.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients](../../LatticeHalfFockChargedCoefficients.md)
