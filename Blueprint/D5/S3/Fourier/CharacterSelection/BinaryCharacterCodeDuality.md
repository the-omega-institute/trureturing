# Binary Character Code Duality

## Abstract

The binary character code is exactly the orthogonal complement of its relations.

**Definition 1.1 (Standard coordinate pairing).**

Lean statement: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.standardCoordinatePairing`

*Formalization.* `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.standardCoordinatePairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the standard dot-product bilinear form on the finite coordinate space.

**Definition 1.2 (Character relation space).**

Lean statement: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.characterRelationSpace`

*Formalization.* `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.characterRelationSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coefficient vector is a relation when its linear combination of the character family vanishes.

**Definition 1.3 (Character code).**

Lean statement: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.characterCode`

*Formalization.* `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.characterCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The code is the range of the joint character-profile map into the finite coordinate space.

**Definition 1.4 (Character orthogonal complement).**

Lean statement: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.characterOrthogonalComplement`

*Formalization.* `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.characterOrthogonalComplement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Orthogonal complementation is taken relative to the named standard coordinate pairing.

**Theorem 1.5 (Character code is the relation orthogonal).**

$$C_{chi} = R_{chi}^{\perp}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.character_code_eq_relation_space_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For FPOD 93.1 the coefficient field is F2. The Lean theorem proves the same equality over every field.

One inclusion evaluates every vanishing character combination. The reverse inclusion follows from dual-map rank equality, rank-nullity, and nondegeneracy of the dot product.

**Theorem 1.6 (Double orthogonal complementation returns the space).**

$$(S^{\perp})^{\perp} = S.$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.standard_orthogonal_complement_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard dot product is symmetric and nondegenerate, so every subspace of the finite coordinate space equals its double orthogonal complement.

**Theorem 1.7 (General coefficient rings need not satisfy code duality).**

$$z, a: \mathbb{Z}\;\operatorname{range}(z \mapsto 2z) \neq \operatorname{ker}(a \mapsto 2a)^{\perp}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.field_coefficients_are_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the integers, the single functional given by multiplication by two has zero relation space, but its realized code is only the even integers rather than the full orthogonal.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.characterCode`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.characterOrthogonalComplement`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.characterRelationSpace`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.character_code_eq_relation_space_orthogonal`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.field_coefficients_are_necessary`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.standardCoordinatePairing`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.standard_orthogonal_complement_involutive`
