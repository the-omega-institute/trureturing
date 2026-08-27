# Finite and Prime-Power Residuals

## Abstract

Finite residuals lie below prime-power residuals, and A5 makes this strict.

**Theorem 1.1 (All finite quotients leave a smaller kernel).**

$$\operatorname{finiteResidual}(G) \le \operatorname{primePowerResidual}(G).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.finite_residual_le_prime_power_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime-power quotient indices form a subfamily of all finite quotient indices. Intersecting the larger family of kernels can only decrease the residual.

**Theorem 1.2 (A5 makes the inclusion strict).**

$$\operatorname{finiteResidual}(A_{5}) < \operatorname{primePowerResidual}(A_{5}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.alternating_five_strict_residual_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For A5 the all-finite residual is trivial while the residual from all finite p-group quotients is the whole group.

**Theorem 1.3 (Factoring the order does not decompose the quotients).**

$$\operatorname{card}(A_{5}) = 2^{2} \times 3 \times 5 \land \operatorname{finiteResidual}(A_{5}) \neq \operatorname{primePowerResidual}(A_{5}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.order_factorization_does_not_force_residual_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A5 has order 2^2 times 3 times 5, yet its two residuals differ. Lagrange and Sylow control orders and subgroups; they do not express a finite group as a limit of its p-group quotients.

**Theorem 1.4 (The trivial group gives equality).**

$$\operatorname{finiteResidual}(\operatorname{trivialSubgroup}(A_{5})) = \operatorname{bottomSubgroup}(\operatorname{trivialSubgroup}(A_{5})) \land \operatorname{primePowerResidual}(\operatorname{trivialSubgroup}(A_{5})) = \operatorname{bottomSubgroup}(\operatorname{trivialSubgroup}(A_{5})) \land \neg(\operatorname{finiteResidual}(\operatorname{trivialSubgroup}(A_{5})) < \operatorname{primePowerResidual}(\operatorname{trivialSubgroup}(A_{5}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.trivial_group_degenerate_case` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the one-element group both residuals are the bottom subgroup, so the general inclusion is equality and cannot be strict.

**Theorem 1.5 (A p-group supplies the extra structure for equality).**

$$\operatorname{Prime}(p) \land \operatorname{IsPGroup}(p, G) \Rightarrow \operatorname{finiteResidual}(G) = \operatorname{primePowerResidual}(G).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.p_group_residual_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If G is a p-group and p is prime, every finite quotient of G is again a p-group. Thus every all-finite kernel already occurs in the prime-power family. No finiteness assumption on G is needed.

**Theorem 1.6 (The finite simple case is maximally separated).**

$$\operatorname{IsSimpleGroup}(A_{5}) \land \operatorname{finiteResidual}(A_{5}) = \operatorname{bottomSubgroup}(A_{5}) \land \operatorname{primePowerResidual}(A_{5}) = \operatorname{topSubgroup}(A_{5}) \land \operatorname{primePowerQuotientObserver}(A_{5}) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.alternating_five_simple_group_case` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A5 is simple, its all-finite residual is bottom, its all-prime-power residual is top, and its joint prime-power observer is trivial.

**Theorem 1.7 (The p-group assumption cannot be removed).**

$$\operatorname{Prime}(2) \land \neg\operatorname{IsPGroup}(2, A_{5}) \land \operatorname{finiteResidual}(A_{5}) \neq \operatorname{primePowerResidual}(A_{5}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.p_group_assumption_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A5 is not a 2-group, while its finite and prime-power residuals are unequal. Thus primality alone does not imply equality.

**Theorem 1.8 (Primality cannot be removed).**

$$\neg\operatorname{Prime}(60) \land \operatorname{IsPGroup}(60, A_{5}) \land \operatorname{finiteResidual}(A_{5}) \neq \operatorname{primePowerResidual}(A_{5}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.prime_parameter_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib defines the raw IsPGroup predicate for every natural parameter. At the composite parameter 60, A5 satisfies that predicate but its finite and prime-power residuals remain unequal.

## References

- Truth anchor: `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.alternating_five_simple_group_case`
- Truth anchor: `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.alternating_five_strict_residual_separation`
- Truth anchor: `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.finite_residual_le_prime_power_residual`
- Truth anchor: `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.order_factorization_does_not_force_residual_equality`
- Truth anchor: `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.p_group_assumption_is_necessary`
- Truth anchor: `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.p_group_residual_equality`
- Truth anchor: `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.prime_parameter_is_necessary`
- Truth anchor: `D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual.trivial_group_degenerate_case`
- Dependency: [D5/S3/Factorization/PrimePowers/AlternatingFiveResidualSeparation](../PrimePowers/AlternatingFiveResidualSeparation.md)
