# Finite Prime-Power Quotient Completeness

## Abstract

Finite prime-power quotient completeness is equivalent to nilpotence.

**Theorem 1.1 (Finite prime-power quotient completeness characterizes nilpotence).**

$$\begin{gathered}\forall G: \operatorname{Type},\\{}(\operatorname{Group}(G) \land \operatorname{Finite}(G)) \Rightarrow\\{}\operatorname{TFAE}(\operatorname{Injective}(\operatorname{primePowerQuotientObserver}(G)),\\{}\operatorname{primePowerResidual}(G) = \operatorname{trivialSubgroup}(G),\\{}\exists \iota: \operatorname{Type}, P: \iota \to \operatorname{Type}, prime: \iota \to \mathbb{N},\\{}\operatorname{Finite}(\iota) \land (\forall i: \iota, \operatorname{Group}(P(i))) \land (\forall i: \iota, \operatorname{Finite}(P(i))) \land\\{}(\forall i: \iota, \operatorname{Prime}(prime(i)) \land \operatorname{IsPGroup}(prime(i), P(i))) \land\\{}\exists embedding: \operatorname{MonoidHom}(G, \prod_{i: \iota} P(i)), \operatorname{Injective}(embedding),\\{}\operatorname{Nilpotent}(G),\\{}\operatorname{Nonempty}(\operatorname{MonoidEquiv}(\prod_{p: \operatorname{primeFactors}(\operatorname{NatCard}(G))} \prod_{S: \operatorname{Sylow}(p, G)} \operatorname{carrier}(S), G))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FinitePrimePowerQuotientCompleteness.finite_prime_power_quotient_completeness_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite group G, index the normal subgroups whose canonical quotients are p-groups for some prime p. Their quotient maps construct the joint observer, and their kernels construct the prime-power residual by intersection.

The theorem states all five equivalent conditions publicly: joint faithfulness, trivial residual, an embedding into a finite product of finite p-groups, nilpotence, and decomposition as the product of the Sylow subgroups.

The quotient observer has the displayed residual as its kernel. A faithful observer itself gives the finite product embedding; conversely, coordinate kernels turn any such embedding into joint quotient faithfulness.

Finite products of p-groups are nilpotent and their subgroups remain nilpotent. Mathlib's finite nilpotence theorem supplies the exact equivalence with the Sylow direct-product decomposition.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/FinitePrimePowerQuotientCompleteness.finite_prime_power_quotient_completeness_tfae`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientJointKernel](../../ConceptDynamics/Faithfulness/FiniteQuotientJointKernel.md)
