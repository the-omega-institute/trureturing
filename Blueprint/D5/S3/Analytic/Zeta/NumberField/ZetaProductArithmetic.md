# Zeta Product Arithmetic

## Abstract

Zeta Product Arithmetic.

**Definition 1.1 (galois Character).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.galoisCharacter`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.galoisCharacter` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

A character of Gal(L/K) valued in ℂ^×.

**Definition 1.2 (galois Character On Ideal).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.galoisCharacterOnIdeal`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.galoisCharacterOnIdeal` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The multiplicative extension of a Galois character χ to the nonzero ideals of 𝓞 K (Sharifi Notation 7.1.17): on a prime 𝔭 it is χ(Frob 𝔭) if 𝔭 is unramified in L and 0 otherwise, extended completely multiplicatively via the prime factorisation. The L-function coefficient χ(𝔞).

**Definition 1.3 (frobenius Ideal).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.frobeniusIdeal`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.frobeniusIdeal` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The Gal(L/K)-valued completely-multiplicative ideal Frobenius: on a prime 𝔭 it is the chosen representative (frobeniusClass K L 𝔭).out of the Frobenius conjugacy class (a genuine group element since Gal(L/K) is abelian, so the class is a singleton), extended completely multiplicatively over the prime factorisation. Companion of galoisCharacterOnIdeal: the character value is χ applied to this element (Helper 1). The Multiset.prod over the (unordered) prime factors needs commutativity, supplied by IsMulCommutative Gal(L/K).

**Theorem 1.4 (Zeta Product Arithmetic).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.unramifiedIn_of_coprime_absNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.unramifiedIn_of_coprime_absNorm` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

A nonzero prime of 𝓞 K whose norm is coprime to m is unramified in L = K(μ_m): a ramified prime would divide the different ideal, which divides (aeval ζ (minpoly 𝓞K ζ).derivative) by the conductor formula; since minpoly ∣ X^m − 1, that derivative value divides m·ζ^{m−1}, so m ∈ 𝔓, hence (m) ≤ 𝔭 and N𝔭 ∣ N((m)) = m^d, contradicting coprimality.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.frobeniusIdeal`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.galoisCharacter`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.galoisCharacterOnIdeal`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.unramifiedIn_of_coprime_absNorm`
- Dependency: [D5/S3/Arith/Lattices/Counting/LatticePointCount](../../../Arith/Lattices/Counting/LatticePointCount.md)
- Dependency: [D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCount](../../../Arith/PrimeIdeals/NormResidue/IdealCongruenceCount.md)
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/CyclotomicNormResidue](../../../Factorization/Galois/Chebotarev/CyclotomicNormResidue.md)
- Dependency: [D5/S3/Factorization/Galois/Chebotarev/Frobenius](../../../Factorization/Galois/Chebotarev/Frobenius.md)
