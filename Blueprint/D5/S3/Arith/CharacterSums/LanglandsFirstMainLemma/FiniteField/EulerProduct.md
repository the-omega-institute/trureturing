# Monic-weight Euler product

## Abstract

The closed-point power identity for a multiplicative monic-polynomial weight.

**Theorem 1.1 (Vanishing degree sums give signed closed-point powers).**

Lean statement: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/EulerProduct.closedPoint_power_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/EulerProduct.closedPoint_power_identity` (`✓ std3`). ∎

*Citation.* fukubillueda-web contributors (2026). *epsilon_FML finite-field Hasse–Davenport supplier*. URL: <https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed>.

*Commentary.*

Let k be a field with Fintype k and w : MonicWeight k ℂ. Write Aₙ for the sum of w(P) over monic polynomials of degree n, and Bᵣ for the sum over degrees e dividing r of e times the sum of w(Q)^(r/e) over monic irreducibles Q of degree e. If Aₙ = 0 for every n ≥ 2, then for every positive r, -Bᵣ = (-A₁)^r. There is no nonvanishing assumption on w.

Unique factorization identifies monic polynomials with multisets of monic irreducibles. The formal generating series L(T) with coefficients Aₙ satisfies L′ = L times the series with coefficients Bᵣ at T^(r - 1). Since A₀ = 1, the vanishing hypothesis reduces L to 1 + A₁T; comparing coefficients yields the signed power identity. All series here are formal.

HasseDavenportLift invokes closedPoint_power_identity with w = gaussPolynomialWeight χ⁻¹ ψ, with vanishing supplied by gaussPolynomialWeight_degreeSum_eq_zero under ψ ≠ 1, and r = Module.finrank k K > 0. Its closed-point and degree-one identifications turn Bᵣ into the lifted ordinary Gauss sum and A₁ into the base ordinary Gauss sum. CharacterAPI's leading-minus normalization gives the exact Hasse–Davenport lift.

Source: epsilon_FML at immutable commit b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, LanglandsFirstMainLemma/FiniteField/EulerProduct.lean; Apache-2.0. The exact license and original source hashes are in Library/Fourier/epsilonfml2026hassedavenport.md. This is attributed upstream reuse, with no new theorem or open-problem resolution claimed.

Supplier escape registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/5214: the original finite-field character/norm/trace telescope has no supplied faithful enrolled template with compiled audit evidence. This narrative does not complete that audit.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/EulerProduct.closedPoint_power_identity`
- Dependency: [D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/PolynomialWeights](PolynomialWeights.md)
