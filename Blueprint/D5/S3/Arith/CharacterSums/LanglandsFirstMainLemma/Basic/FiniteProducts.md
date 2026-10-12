# Prime-field finite products

## Abstract

Prime-field power sums and products in the retained character-sum supplier.

**Theorem 1.1 (Power sums in an injective unit realization).**

Lean statement: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts.sum_primeField`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts.sum_primeField` (`✓ std3`). ∎

*Citation.* fukubillueda-web contributors (2026). *epsilon_FML finite-field Hasse–Davenport supplier*. URL: <https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed>.

*Commentary.*

For a prime p, a natural exponent r, a commutative domain R, and an injective group homomorphism ω from (ZMod p)ˣ to Rˣ, the sum of (ω(j) : R)^r over all j is p - 1 cast into R if p - 1 divides r, and is zero otherwise. The homomorphism j ↦ (ω(j) : R)^r is trivial exactly in the divisible case; character orthogonality gives the sum.

**Theorem 1.2 (Scaled prime-field product).**

Lean statement: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts.prod_one_add_primeField`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts.prod_one_add_primeField` (`✓ std3`). ∎

*Citation.* fukubillueda-web contributors (2026). *epsilon_FML finite-field Hasse–Davenport supplier*. URL: <https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed>.

*Commentary.*

For a field K of characteristic p and any ρ in K, the product over j in ZMod p of 1 + cast(j)ρ equals 1 - ρ^(p - 1). The proof rescales the factorization of X^p - X; ρ = 0 is included separately.

This module imports Mathlib directly. CharacterAPI imports this module, and HasseDavenportLift imports CharacterAPI. This is a retained import dependency. Neither displayed prime-field identity is invoked by the selected Hasse–Davenport proof; the lifting argument uses general finite-field characters and monic-polynomial weights.

Source: epsilon_FML at immutable commit b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, LanglandsFirstMainLemma/Basic/FiniteProducts.lean; Apache-2.0. The exact license and original source hashes are in Library/Fourier/epsilonfml2026hassedavenport.md. These are attributed upstream results, with no new theorem or open-problem resolution claimed.

Supplier escape registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/5214: the original finite-field character/norm/trace telescope has no supplied faithful enrolled template with compiled audit evidence. This narrative does not complete that audit.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts.prod_one_add_primeField`
- Truth anchor: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts.sum_primeField`
