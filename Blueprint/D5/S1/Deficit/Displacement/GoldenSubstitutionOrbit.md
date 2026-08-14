# Golden Substitution Orbit

## Abstract

Golden substitution preserves prime support and admits uniform orbitwise error bounds.

**Theorem 1.1 (The hidden product is always nonzero).**

$$\forall n\in\mathbb{N},\ nS(n)\neq0$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.nS_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden product is a finite product of powers of primes in the original factorization support. Every such prime is positive, so every factor is positive and the whole product is positive. The empty product cases, including the input zero, are therefore covered without a separate hypothesis.

**Theorem 1.2 (One substitution preserves the prime radical).**

$$\forall n\in\mathbb{N},\ \operatorname{rad}(nS(n)) = \operatorname{rad}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.primeRadical_nS` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorization of nS maps goldenSubstStart across the original exponents. That map fixes zero and is injective because substitution starts are strictly increasing, so mapping the exponent range leaves the finite support unchanged. The products of the distinct supported primes, hence the radicals, are equal. This support argument also covers zero unconditionally.

**Theorem 1.3 (Every orbit iterate preserves the prime radical).**

$$\forall k, n\in\mathbb{N},\ \operatorname{rad}(nS^{k}(n)) = \operatorname{rad}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.primeRadical_nS_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the iterate count repeatedly applies the one-step radical invariance. The zeroth iterate is the identity, and composing one more nS leaves the radical fixed again. Thus the entire orbit remains on the same set of prime divisors.

**Theorem 1.4 (The frozen contraction bound is uniform along the orbit).**

$$\forall k, n\in\mathbb{N},\ n\neq0 \implies \lvert\lambda_{-}(nS^{k}(n))\rvert \leq \varphi^{-1} \cdot \log{\operatorname{rad}(n)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.abs_lambdaMinus_nS_iterate_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every orbit point is nonzero when the starting value is nonzero: the zeroth point is the start, while every later point is an nS value and is always nonzero. The existing single-number contraction theorem applies at each point. Orbitwise radical invariance then replaces its radical by the one fixed at the start.

**Theorem 1.5 (Accumulated logarithmic displacement has a geometric bound).**

$$\forall k, n\in\mathbb{N},\ n\neq0 \implies \lvert\log{nS^{k}(n)} - \varphi^{k} \cdot \log{n}\rvert \leq \left(\varphi^{k} - 1\right) \cdot \log{\operatorname{rad}(n)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.abs_log_nS_iterate_sub_goldenRatio_pow_mul_log_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the next orbit point, the logarithmic displacement splits into the current contraction error plus phi times the displacement already accumulated. The triangle inequality, the uniform contraction bound, and the induction hypothesis therefore give a recurrence with one phi-inverse radical term per step. The identity phi minus phi inverse equals one converts that recurrence exactly into the coefficient phi to the kth power minus one.

## References

- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.abs_lambdaMinus_nS_iterate_le`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.abs_log_nS_iterate_sub_goldenRatio_pow_mul_log_le`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.nS_ne_zero`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.primeRadical_nS`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.primeRadical_nS_iterate`
- Dependency: [D5/S1/Deficit/Displacement/GoldenContractionRadicalBound](GoldenContractionRadicalBound.md)
