# Finite Native Correction Translation

## Abstract

Finite Native Correction Translation.

The original Corr is retained. correctedSource only applies the inverse of optionEquivLeft to the existing correctionPolynomial; it is not another state-field or correction assignment. The differential connection acts on the shift variable t by -t^2 and on each source oscillator X(i,k) by (k+1)X(i,k+1), minus the actual charge-weighted pair insertions.

**Theorem 1.1 (Original Corr applied to original sector translation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionTranslation.Corr_sectorTranslation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionTranslation.Corr_sectorTranslation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every rank, charge and finite oscillator polynomial, Corr of the literal sectorTranslation equals the finite correction readout of the explicit differential connection plus the charge-weighted original insertions. The singleton recurrence retains halfBinomial 1=-1/2. The pair recurrence is proved for all positive source weights; the derivation commutator is checked on every original polynomial variable, then extended by the universal derivation property. The existing correctionWord permutation and monomial basis are consumed to identify actual Corr with insertion on arbitrary polynomials. Polynomial induction uses the literal oscillatorDerivation and chargePolynomial, not a translation operator defined by the wanted identity.

All operations in this correction theorem are finite polynomial operations. No infinite normal-mode interchange is claimed here. LatticeHalfFockOriginalTranslation joins this finite recurrence to the genuine charged physical derivative and the normal-polynomial evaluation laws. This correction theorem alone is not the all-state Ytw translation theorem or a twisted Jacobi certificate.

The Reg mirror proves the unrestricted dependent source/readout equivalence, including rank zero. Its typed obligations do not establish declared_validated source admission: lawful enrolled-template application, variation, sensitivity, observational dependence and source selection remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectionTranslation.Corr_sectorTranslation`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](LatticeHalfFockFiniteCorrection.md)
