# Ground exchange through every corrected-field coefficient

## Abstract

Actual charge-character covariance of the complete corrected twisted field.

Let D be any finite-rank integral symmetric even lattice datum, hu:IsUnit D.G.det, and a any lattice charge. Write G_a for the existing actualGroundInsert D hu (groundAction D hu a), and chi_a for the ordinary charge character in Lattice/NormFourPeirceInvolution. Its value on charge b is multiplication by paritySign(bilinear D a b). The ordinary carrier and the actual twisted tensor carrier are different spaces.

**Theorem 1.1 (Ground insertion implements the ordinary character on the full corrected field).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockGroundCharacter.correctedField_ground_character`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockGroundCharacter.correctedField_ground_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every source v, integer Hahn exponent e and actual tensor vector x, G_a((correctedField v).coeff e x) equals (correctedField (chi_a v)).coeff e (G_a x). No norm-four assumption, preferred model, source identification, fixedness, parity, mode covariance or commutator premise is supplied. The charged coefficient calculation uses the existing actual ground exchange. Ground insertion commutes with every tensor jet, so both normal-order branches retain that same charge phase for arbitrary words. Existing pointwise finite support moves insertion and scalar multiplication through the full word sums. Linearity extends this to every source polynomial, the actual finite Corr, every shift and the complete finite charge sum.

The ordinary full-carrier, all-mode stateField_chi theorem remains the ordinary supplier. Existing actualTensorL0_groundInsert_commute and actualGroundInsert_preserves_grade already give energy and grade preservation. The accepted NormFourFirstGradeSpectrum identification of the actual parity minus grade with its physical space remains the spectral supplier. No spectrum or numerical trace is reconstructed here.

For fixed-source physical applications, actualParity concerns oscillator parity, whereas G_a acts on the ground factor. Source character sign and target parity are distinct parameters. The existing fixedParitySlice uses coefficient 2*e, so that is the coefficient to specialize in this identity. Restricting carriers requires preserving source theta-fixedness and target parity; this all-carrier coefficient theorem does not define a new restricted field. Norm-four involutivity is a separate existing ground square calculation, not a hypothesis of the character identity.

This is an all-integer-coefficient linear character identity, derived from the classical lattice construction. It does not establish VOA intertwining-operator Jacobi, orbifold gluing, all-grade Ising or Miyamoto fusion, a Monster VOA, or the complete string-theory and AdS/CFT bridge. Those objectives remain incomplete. No literature novelty is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockGroundCharacter.correctedField_ground_character`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField](LatticeHalfFockParityField.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution](../Lattice/NormFourPeirceInvolution.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts](../LatticeHalfFockGroundProducts.md)
