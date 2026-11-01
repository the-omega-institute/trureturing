# All-state original-source BPZ

## Abstract

All-state original-source BPZ

The pairing is the complex bilinear OriginalSourcePairing.sourcePairing on the original finite-charge oscillator-polynomial Carrier. The field is literally LatticeAllStateField.Y. D ranges over every symmetric even integral LatticeData for which the integer determinant is a unit, including rank zero and indefinite Gram matrices. The grade is the exact signed coefficient-support grade of LatticePositiveEnergy; no positivity or finite dimension of that grade is required.

**Theorem 1.1 (Canonical all-state BPZ).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/AllStateTranspose.sourcePairing_allState`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/AllStateTranspose.sourcePairing_allState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu : IsUnit D.G.det, integers d and m, actual source a in grade D d, and arbitrary original-carrier inputs u and v, sourcePairing(D,(Y(D,a)[[m]])u,v) equals (-1)^d times the sum over j in Finset.range(R(a)+1) of inverse(j!) times sourcePairing(D,u,(Y(D,L1^j a)[[2*d-j-m-2]])v). Here (-1)^d is complex integer zpow, L1 is literally sugawaraMode D ((gramComplex D) inverse) 1, and R(a) is literally a.support.sup(fun alpha => weightedTotalDegree(sourceWeight D)(a alpha)). The inverse in L1 is the matrix inverse of gramComplex D. The factorial is cast to the complex numbers before inversion.

The charged base is the existing sourcePairing_rawCoeff, with the actual coefficient-to-mode conversion and the identity twice chargeEnergy equals the charge norm. A terminating induction removes the first oscillator of a word. consumed_normal_product_form applies to the remaining word, the finite support of its actual flowPolynomial, the proved neutral-current transpose, and the charge zero-mode covariance derived from charge_homogeneity. The existing multiplication_recursion identifies each insertion with the original polynomial state field; no transpose of a transformed tail is an induction premise.

The linear polynomial coefficient readout collects the insertion terms with j=l+p-s and the deletion term with j=l+p+1. The mode becomes 2*d-j-m-2 in both cases, and the common sign is the integer power (-1)^d. The variable polynomial formula consumes flowPolynomial_eq_sum and the existing variable powers, including the charge term. flowPolynomial_eq_sum already uses flowPolynomial_coeff for every polynomial and index, so no separate factorial identification or alternate flow is introduced.

The true charge and monomial supports of a are expanded linearly. mem_grade_iff forces every supported monomial to have the common signed energy d. Its oscillator weight is bounded by the exact R(a). The existing monomial nilpotence supplies the padded flow sum at that bound, and sugawara_pow_single identifies every sector power with the actual inverse-Gram Sugawara power. The zero state and empty supports are covered by the same finite linear identities.

This is standard lattice vertex-algebra invariant-form theory, using Bakalov--Kac, math/0402315v1, section 4.1 for the actual lattice-field conventions. Imported normal-product and Sugawara constructions retain their Carnahan and Kalle Kytola attributions, and Mathlib retains its Apache-2.0 license and authorship. No novelty claim is made. This theorem is one unit toward the broader Monster, VOA, CFT, anomaly, fusion, string-theory and AdS formalization; it does not establish that whole goal.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/AllStateTranspose.sourcePairing_allState`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule](../Sectors/LatticeDualCosetModule.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner](../Sectors/LatticeSectorIntertwiner.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/ChargedRawTranspose](ChargedRawTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose](NormalScalarTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws](SourcePairingLaws.md)
- Dependency: [D5/S3/VertexAlgebra/SourceMobius/OriginalCarrier](../SourceMobius/OriginalCarrier.md)
