# The norm-four character on the original orbifold

## Abstract

The norm-four character on the original orbifold

Let D be lattice data with hu : IsUnit D.G.det, a : Charge D and s : ℂ. Write B for bilinear D and C for the original fixed and negative twisted carrier. `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Carrier`

**Definition 1.1 (Block action on the original carrier).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.character`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.character` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endomorphism A applies the charge character to the fixed sector and inserts (−s) times the lifted ground action in the negative twisted sector. On opposite charges the character phases agree, so the character commutes with reflection. The ground insertion commutes with the oscillator parity operator. `D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.chi_single`

**Theorem 1.2 (The normalized action is involutive).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.character_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.character_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If B(a,a) = 4 and s² = 1, then A(Ax) = x for every x in C. The charge character is involutive, and the norm-four ground action squares to the identity. Tensor insertion preserves the square, and (−s)² = 1. `D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.chi_involutive`, `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.ground_square`

**Definition 1.3 (Linear equivalence on the original carrier).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.symmetry`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.symmetry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the norm and sign hypotheses, the forward and inverse maps of S : C ≃ₗ[ℂ] C both apply A. `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.character_involutive`

**Theorem 1.4 (All modes with a fixed source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.Y_fixed_character`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.Y_fixed_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)) and write Y for Y D hu hD. For every n : ℤ, u : FixedCarrier D and v : C, A(Y((u, 0))[n] v) = Y(A((u, 0)))[n](Av). The fixed mode uses charge-character covariance and the negative twisted mode uses corrected-field covariance at coefficient 2(−n−1). `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_fixed_ncoeff_apply`, `D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.stateField_chi`, `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockGroundCharacter.correctedField_ground_character`

**Theorem 1.5 (Intertwining every mode on the original carrier).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.Y_character`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.Y_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume hD as above, D.rank = 24, B(a,a) = 4 and s² = 1. For every n : ℤ and all u, v : C, S(Y(u)[n] v) = Y(Su)[n](Sv) at the original normalized mode n.

The signed insertion commutes with twisted translation, which is the zero mode of the neutral stress state. It therefore commutes with the powers of translation in the original right coefficient. The injective insertion carries the sum to the transformed sum term by term. `D5/S3/VertexAlgebra/TwistedGround/OriginalRightSkew.originalRightCoefficient`

The source pairing pairs opposite charges. The twisted pairing is invariant under the simultaneous signed insertion, by ground pairing invariance and (−s)² = 1. The insertion preserves twisted energy and commutes with L(1). Together with corrected-field covariance these facts preserve each summand of the normalized coefficient on homogeneous inputs. `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_pairing`

Evaluation of the fixed-grade pairing recovers the homogeneous functional and identifies the transformed output. The finite homogeneous tensor tests extend the identity to both arbitrary twisted inputs. The four blocks then give covariance on C. `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.originalI_homogeneous`, `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMContraction.sourceGradePairingEquiv_evaluation`, `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_ext`, `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.Y_fixed_character`, `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_ncoeff_apply`

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockGroundCharacter.correctedField_ground_character`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.ground_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.chi_involutive`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.chi_single`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.stateField_chi`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Carrier`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_fixed_ncoeff_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.Y_ncoeff_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.Y_character`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.Y_fixed_character`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.Y_fixed_character`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.character`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.character_involutive`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.character_involutive`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNormFourCharacter.symmetry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.originalI_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMContraction.sourceGradePairingEquiv_evaluation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_ext`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalRightSkew.originalRightCoefficient`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockGroundCharacter](../../HalfFock/LatticeHalfFockGroundCharacter.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades](../../HalfFock/NormFourLowestGrades.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField](OriginalOrbifoldField.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs](../OriginalFourMInputs.md)
