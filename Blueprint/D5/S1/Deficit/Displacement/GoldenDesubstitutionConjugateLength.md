# Golden Desubstitution on Conjugate-Face Length

## Abstract

Golden substitution of prime exponents becomes Zeckendorf displacement in the conjugate-face length.

**Theorem 1.1 (The substituted conjugate-face length is a displacement sum).**

$$\lambda_{-}(nS n) = \sum_{p} betaContraction(displacementDecode(vp)) \cdot \log p$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDesubstitutionConjugateLength.lambdaMinus_nS_eq_displacement_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden product nS and its factorization come from the expansion-face bridge. Expanding lambdaMinus over that factorization applies betaContraction to every goldenSubstStart exponent. The repository's golden substitution boundary theorem then replaces each transformed exponent by displacementDecode, the one-step upward shift of its canonical Zeckendorf digits.

**Theorem 1.2 (Substitution changes conjugate length by exponentwise displacement increments).**

$$\lambda_{-}(nS n) - \lambda_{-}(n) = \sum_{p} \left(betaContraction(displacementDecode(vp)) - betaContraction(vp)\right) \cdot \log p$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDesubstitutionConjugateLength.lambdaMinus_nS_sub_lambdaMinus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the original conjugate-face length from the substituted one combines the two finite prime sums term by term. Each summand is the change from betaContraction at the original exponent to betaContraction at its Zeckendorf displacement decode, weighted by the logarithm of the corresponding prime.

## References

- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDesubstitutionConjugateLength.lambdaMinus_nS_eq_displacement_sum`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDesubstitutionConjugateLength.lambdaMinus_nS_sub_lambdaMinus`
- Dependency: [D5/S1/Deficit/Displacement/GoldenDesubstitutionLength](GoldenDesubstitutionLength.md)
