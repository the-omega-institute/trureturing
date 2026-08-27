# Observer-Type Irreplaceability for A5

## Abstract

A5 is invisible to every finite p-group observer but has a faithful characteristic-five linear observer.

**Theorem 1.1 (Prime-power quotient and residue-linear observers are not interchangeable).**

$$\exists G, \operatorname{FiniteGroup}(G) \land \operatorname{GroupIso}(G, A_{5}) \land\\{}(\forall p \in \mathbb{N}, \operatorname{Prime}(p) \Rightarrow \forall P, (\operatorname{FiniteGroup}(P) \land \operatorname{IsPGroup}(p, P)) \Rightarrow \forall q \in \operatorname{Hom}(G, P), \neg\operatorname{Injective}(q)) \land\\{}(\exists V, \operatorname{Module}(\operatorname{ZMod}(5), V) \land \exists \rho \in \operatorname{Hom}(G, \operatorname{GL}(\operatorname{ZMod}(5), V)), \operatorname{Injective}(\rho)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ObserverTypes/AlternatingFiveObserverTypeIrreplaceability.alternating_five_observer_type_irreplaceability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a finite group G isomorphic to A5 such that, for every prime p, every finite p-group P, and every homomorphism from G to P, the homomorphism is noninjective. This universal clause is inherited from the repository theorem that all such homomorphisms are trivial.

For the same group G there is a module V over Z/5Z and an injective homomorphism from G to the general linear group of V. The witness is the left regular representation, so the existential observer is constructed rather than postulated.

## References

- Truth anchor: `D5/S3/Factorization/ObserverTypes/AlternatingFiveObserverTypeIrreplaceability.alternating_five_observer_type_irreplaceability`
- Dependency: [D5/S3/Factorization/PrimePowers/SimpleToPGroupTrivial](../PrimePowers/SimpleToPGroupTrivial.md)
