# Langlands-normalized Hasse–Davenport lifting

## Abstract

The exact Langlands-normalized Hasse–Davenport lift for finite-field Gauss sums.

**Theorem 1.1 (Hasse–Davenport lift).**

Lean statement: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.hasseDavenportLift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.hasseDavenportLift` (`✓ std3`). ∎

*Citation.* fukubillueda-web contributors (2026). *epsilon_FML finite-field Hasse–Davenport supplier*. URL: <https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed>.

*Commentary.*

For fields k and K with finite underlying types, an algebra structure, a finite multiplicative character χ, and a finite additive character ψ with ψ unequal to the trivial character, the theorem identifies the Langlands-normalized Gauss sum after norm and trace pullback with the base Gauss sum raised to the finite extension degree. The multiplicative character is unrestricted, so the trivial multiplicative character is included.

The normalization is langlandsGaussSum(χ, ψ) = -gaussSum(χ⁻¹, ψ). The theorem and proof are reused from epsilon_FML at commit b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed. The argument identifies closed-point contributions through minimal polynomials and actual algebraic norm and trace, then uses the Euler product to obtain the power identity. The inverse character and leading minus sign cancel the ordinary lifting parity sign in every degree. This supplies the classical Hasse–Davenport theorem through attributed upstream reuse.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.hasseDavenportLift`
- Dependency: [D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI](CharacterAPI.md)
- Dependency: [D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/EulerProduct](EulerProduct.md)
- Dependency: [D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Extension](../LocalField/Extension.md)
