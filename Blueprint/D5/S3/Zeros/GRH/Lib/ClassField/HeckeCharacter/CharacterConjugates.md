# Character Conjugates

## Abstract

Character Conjugates

Existence, finiteness and algebraicity of tame algebraic characters of the norm-one torus. p-adic absolute value of an algebraic Hecke character is given by its weights. Conjugates of algebraic characters: modulus one, permuted weight, conjugated tame part.

**Theorem 1.1 (exists_conj).**

Lean statement: `D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharacterConjugates.exists_conj`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharacterConjugates.exists_conj` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let μ have weight e and tame part ψ, and let σ ∈ Aut ℂ permute the CM type: σ∘Φ_v = Φ_{p(v)}. Then some ν has weight e∘p⁻¹, tame part σ∘ψ, and ν(u) = σ(μ(u)) whenever u has archimedean component 1.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharacterConjugates.exists_conj`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/ExtendCharacter](../GreenbergWiles/ExtendCharacter.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharacterLevels](CharacterLevels.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Places/UnramifiedCharacters](../Places/UnramifiedCharacters.md)
