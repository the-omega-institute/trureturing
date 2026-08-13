# Golden Desubstitution on Expansion-Face Length

## Abstract

Golden substitution of prime exponents becomes Zeckendorf displacement in the expansion-face length.

**Theorem 1.1 (The substituted expansion-face length is a displacement sum).**

$$\lambda_{+}(nS n) = \sum_{p} betaReal(displacementDecode(vp)) \cdot \log p$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDesubstitutionLength.lambdaPlus_nS_eq_displacement_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden product nS applies goldenSubstStart to every exponent in the prime factorization. Its own factorization therefore has exactly those transformed exponents. Expanding lambdaPlus and using the repository's golden substitution boundary theorem replaces each transformed exponent by displacementDecode, the one-step upward shift of its canonical Zeckendorf digits.

**Theorem 1.2 (Substitution changes length by exponentwise displacement increments).**

$$n\neq0 \implies \lambda_{+}(nS n) - \lambda_{+}(n) = \sum_{p} \left(betaReal(displacementDecode(vp)) - betaReal(vp)\right) \cdot \log p$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDesubstitutionLength.lambdaPlus_nS_sub_lambdaPlus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero n, subtracting the original expansion-face length from the substituted one combines the two finite prime sums term by term. Each summand is the change from betaReal at the original exponent to betaReal at its Zeckendorf displacement decode, weighted by the logarithm of the corresponding prime.

## References

- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDesubstitutionLength.lambdaPlus_nS_eq_displacement_sum`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDesubstitutionLength.lambdaPlus_nS_sub_lambdaPlus`
- Dependency: [D5/S1/Deficit/DoubleFaceLength](../DoubleFaceLength.md)
- Dependency: [D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf](../../Words/Powers/GoldenDesubstitutionZeckendorf.md)
