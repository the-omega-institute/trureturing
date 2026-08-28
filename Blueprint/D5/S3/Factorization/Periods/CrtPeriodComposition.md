# CRT Period Composition

## Abstract

Prime-power CRT coordinates compose the phase period by least common multiple.

**Theorem 1.1 (Prime-power periods compose by lcm).**

$$\forall m\in \mathbb{N}, m\neq0 \Rightarrow T(m)=\operatorname{lcm}_{p \in \operatorname{PrimeFactors}(m)} T(p^{v_{p}(m)}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Periods/CrtPeriodComposition.phase_period_crt_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero natural modulus, its named phase period is the least common multiple of the periods of the prime powers in its canonical factorization.

The imported finite CRT supplies the ring equivalence. Additive order is invariant under that equivalence, and the order of a finite dependent product is the lcm of coordinate orders.

Primality carries the CRT coprimality argument. The special role of two occurs only inside the already named local period formula T(m)=m/gcd(m,2).

**Lemma 1.2 (The zero modulus is necessarily excluded).**

$$\neg{T(0)=\operatorname{lcm}_{p \in \operatorname{PrimeFactors}(0)} T(p^{v_{p}(0)})}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Periods/CrtPeriodComposition.nonzero_modulus_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero the named period is zero, while primeFactors zero is empty and the Finset lcm of an empty family is one. Thus the nonzero premise cannot be removed from the canonical-factorization statement.

## References

- Truth anchor: `D5/S3/Factorization/Periods/CrtPeriodComposition.nonzero_modulus_is_necessary`
- Truth anchor: `D5/S3/Factorization/Periods/CrtPeriodComposition.phase_period_crt_composition`
- Dependency: [D5/S3/Factorization/PrimePowers/FiniteCrtJoin](../PrimePowers/FiniteCrtJoin.md)
- Dependency: [D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod](../../PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod.md)
