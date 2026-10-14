# Shift and original oscillator weight

## Abstract

Exact weight of the native twisted correction

The construction uses the original singletonPolynomial, pairPolynomial, pairDerivation, insertion, correctionWord and Corr. The auxiliary coordinate none has weight one and coordinate some(i,n) has the original oscillator weight n+1. Neither the original oscillatorEuler nor any physical field is redefined.

**Theorem 1.1 (The actual correction word has its exact original total weight).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.correctionWord_weighted`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.correctionWord_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The real singleton coefficient multiplies the auxiliary coordinate to power n+1. The real pair coefficient multiplies it to the sum of the two original weights, with the actual Gram entry and pairScalar unchanged. correctionWord_matching and labelledRemainders_size supply the exact remaining weight for every repeated occurrence. Strong induction on word length includes empty words, arbitrary charge, nonorthonormal Gram and rank zero.

**Theorem 1.2 (Every nonzero shift coefficient retains weight W minus s).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.correctionWord_coefficient_weight`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.correctionWord_coefficient_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Actual optionEquivLeft coefficient extraction identifies the exponent with optionElim. The additive weight is exactly s plus the remaining oscillator weight. This consequence of correctionWord_weighted is stronger than a shift bound and yields Corr_Euler.

**Theorem 1.3 (Corr intertwines the original Euler operator with the shift count).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.Corr_Euler`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.Corr_Euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every complex finite polynomial p and natural s, oscillatorEuler(Corr(p)[s])+s Corr(p)[s]=Corr(oscillatorEuler(p))[s]. Monomial enumeration has the exact word weight. Polynomial linear extension includes arbitrary finite mixtures; zero and absent coefficients need no homogeneous-input assumption. oscillatorEuler_monomial identifies the original diagonal action on every monomial.

The classical twisted lattice correction is described by FLM and the Dong-Nagatomo and Bakalov-Kac sources. Its exact weight identity supports L0 covariance; it does not establish full twisted Jacobi, fusion, a Monster action, string theory or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.Corr_Euler`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.correctionWord_coefficient_weight`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionGrading.correctionWord_weighted`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](LatticeHalfFockFiniteCorrection.md)
