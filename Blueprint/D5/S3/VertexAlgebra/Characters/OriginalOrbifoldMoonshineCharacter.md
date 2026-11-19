# Original Golay–Leech orbifold moonshine character

## Abstract

The original Golay–Leech orbifold character equals the normalized level-one modular invariant.

**Theorem 1.1 (The character as the Eisenstein cube divided by the discriminant).**

Lean statement: `D5/S3/VertexAlgebra/Characters/OriginalOrbifoldMoonshineCharacter.character_eq_eisensteinCube_div_discriminant_sub_744`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/OriginalOrbifoldMoonshineCharacter.character_eq_eisensteinCube_div_discriminant_sub_744` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shifted conformal zero-mode character of the original Golay–Leech orbifold equals the cube of the weight-four Eisenstein series divided by the level-one discriminant, with 744 subtracted, at every point of the upper half-plane.

At each nonnegative integer weight, the original conformal zero-mode eigenspace is linearly isomorphic to the product of its theta-fixed lattice sector and its negative-parity twisted sector. The character uses the sum of the two dimensions, which equals the full eigenspace dimension at that weight.

Multiplying the character by the discriminant gives a weight-twelve level-one modular form. The proof uses slash invariance, holomorphy and boundedness at the cusp. It subtracts the cube of the weight-four Eisenstein series to obtain a modular form of the same weight.

The constant and linear q coefficients of the character times the discriminant are 1 and −24. The corresponding coefficients of the Eisenstein cube are 1 and 720. Thus the difference has zero constant coefficient and linear coefficient −744.

The zero constant coefficient makes the difference a cusp form. Every weight-twelve level-one cusp form is a scalar multiple of the discriminant. The discriminant has linear q coefficient 1, so comparing linear coefficients gives the scalar −744. The discriminant has no zeros in the upper half-plane, so dividing the resulting identity gives the character formula.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/OriginalOrbifoldMoonshineCharacter.character_eq_eisensteinCube_div_discriminant_sub_744`
