# Eisenstein Prime Coefficient

## Abstract

The prime q-coefficient of a level-one Eisenstein series is the Bernoulli normalization times 1 plus p to the k minus one.

**Theorem 1.1 (Prime q-coefficient).**

$$\forall k, p, primeQCoefficient= bernoulliMultiplier.$$

*Proof.* Machine-checked in Lean as `D5/S1/NumberTheory/ModularForms/EisensteinPrimeCoefficient.eisenstein_qExpansion_coeff_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The q-expansion coefficient theorem reduces the claim to the divisor sum at a prime. The prime divisor description then gives the two terms 1 and p^(k-1).

This is the arithmetic input for a later formalization of the Hecke operator T_p on q-expansions.

## References

- Truth anchor: `D5/S1/NumberTheory/ModularForms/EisensteinPrimeCoefficient.eisenstein_qExpansion_coeff_prime`
