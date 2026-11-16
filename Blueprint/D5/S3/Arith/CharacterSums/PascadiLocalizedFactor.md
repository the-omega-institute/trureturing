# Primitive localized factors

## Abstract

Integrated from the completed pinned singular-cover formalization. Primitive integer factors are selected at the actual residue root and inherit weighted coefficient control. The complementary polynomial after real rescaling is not asserted to be integral. The proof uses the repository Gelfond inequality. The rational-factor lifting helper is exposed for the live prime-cube proof.

Integrated from the completed pinned singular-cover formalization. Primitive integer factors are selected at the actual residue root and inherit weighted coefficient control. The complementary polynomial after real rescaling is not asserted to be integral. The proof uses the repository Gelfond inequality. The rational-factor lifting helper is exposed for the live prime-cube proof.

**Theorem 1.1 (primitive_localized_factor).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.primitive_localized_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.primitive_localized_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The factor is constructed from the original polynomial, preserving exact singularity data.

**Theorem 1.2 (weighted_primitive_localized_factor).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.weighted_primitive_localized_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.weighted_primitive_localized_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Weighted height is inherited by the primitive factor selected at the actual residue root.

**Theorem 1.3 (lift_primitive_rational_factor).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.lift_primitive_rational_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.lift_primitive_rational_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

lift primitive rational factor.

**Theorem 1.4 (weighted_localized_factor_cover).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.weighted_localized_factor_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.weighted_localized_factor_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The cover consists of primitive integer factors of actual original polynomials, and every chosen factor vanishes at the actual residue root.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.lift_primitive_rational_factor`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.primitive_localized_factor`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.weighted_localized_factor_cover`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.weighted_primitive_localized_factor`
- Dependency: [D5/S3/Arith/AbsoluteValues/Heights/Gelfond](../AbsoluteValues/Heights/Gelfond.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiSingularFactorCover](PascadiSingularFactorCover.md)
