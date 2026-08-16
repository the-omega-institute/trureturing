# Prime-Power Criterion

## Abstract

Prime powers are exactly the natural numbers with a unique prime divisor.

**Theorem 1.1 (A natural number is a prime power exactly when its prime divisor is unique).**

$$\forall n \in \mathbb{N},\ \operatorname{IsPrimePow}(n) \iff \exists! p \in \mathbb{N},\ \operatorname{Prime}(p) \land p \mid n$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/PrimePowerCriterion.prime_power_iff_unique_prime_divisor` (`✓ std3`). ∎

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

For every natural number n, being a positive power of a prime is equivalent to the existence of exactly one prime divisor of n. The edge cases zero and one make both sides false, so the equivalence needs no additional lower bound. Pinned Mathlib supplies the exact characterization isPrimePow_iff_unique_prime_dvd; the Lean theorem is only the thinnest repository-addressed wrapper over that upstream truth. This closes only the arithmetic core of the prime-power criterion in appendix E.148. The geometric-spectrum genealogy, maximal-chain count, cyclotomic mechanism, prime zeta identity, growth constant, Tauberian constant, MUB window, and all numerical certificates in the same atom remain outside this claim.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/PrimePowerCriterion.prime_power_iff_unique_prime_divisor`
