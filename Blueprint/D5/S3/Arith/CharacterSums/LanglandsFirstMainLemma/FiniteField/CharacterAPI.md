# Finite-field character interface

## Abstract

Finite-field characters, Langlands-normalized Gauss sums, and norm/trace pullback.

**Definition 1.1 (Inverse-character and leading-minus normalization).**

Lean statement: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI.langlandsGaussSum`

*Formalization.* `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI.langlandsGaussSum` (`✓ std3`).

*Citation.* fukubillueda-web contributors (2026). *epsilon_FML finite-field Hasse–Davenport supplier*. URL: <https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed>.

*Commentary.*

For a field k with Fintype k, FiniteMulChar k is MulChar k ℂ and FiniteAddChar k is AddChar k ℂ. The definition is langlandsGaussSum χ ψ = -gaussSum χ⁻¹ ψ, equivalently the negative sum of χ⁻¹(x)ψ(x) over kˣ. MulChar has value zero at zero, including the trivial multiplicative character. For ψ ≠ 1, the trivial multiplicative character has normalized Gauss sum 1.

**Theorem 1.2 (Norm pullback commutes with character inversion).**

Lean statement: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI.normMulChar_inv`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI.normMulChar_inv` (`✓ std3`). ∎

*Citation.* fukubillueda-web contributors (2026). *epsilon_FML finite-field Hasse–Davenport supplier*. URL: <https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed>.

*Commentary.*

For fields k and K, Finite K, Algebra k K, and any χ in FiniteMulChar k, normMulChar k K χ⁻¹ = (normMulChar k K χ)⁻¹. Here normMulChar χ evaluates χ on Algebra.norm k, while traceAddChar ψ evaluates ψ on Algebra.trace k K. Neither definition replaces the norm or trace by an auxiliary function.

PolynomialWeights consumes FiniteMulChar and FiniteAddChar to construct gaussPolynomialWeight. HasseDavenportLift consumes the Gauss-sum normalization and both pullbacks; its final proof explicitly rewrites by normMulChar_inv. The inverse character and leading minus are required for the power identity in every extension degree. Only the additive character must be nontrivial in the lifting theorem.

Source: epsilon_FML at immutable commit b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, LanglandsFirstMainLemma/FiniteField/CharacterAPI.lean; Apache-2.0. The exact license and original source hashes are in Library/Fourier/epsilonfml2026hassedavenport.md. This is attributed upstream reuse, with no new theorem or open-problem resolution claimed.

Supplier escape registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/5214: the original finite-field character/norm/trace telescope has no supplied faithful enrolled template with compiled audit evidence. This narrative does not complete that audit.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI.langlandsGaussSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI.normMulChar_inv`
- Dependency: [D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts](../Basic/FiniteProducts.md)
- Dependency: [D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField](../LocalField/ResidueField.md)
