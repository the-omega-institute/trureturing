# Full Blind Kernel and Observer-Type Irreplaceability for A5

## Abstract

A5 has a full prime-power blind kernel but a faithful characteristic-five linear observer.

**Theorem 1.1 (Prime-power quotient observation leaves A5 fully blind).**

$$\begin{gathered}\exists G: \operatorname{Type}, [\operatorname{Group}(G)], [\operatorname{Finite}(G)], \operatorname{Nonempty}(\operatorname{GroupIso}(G, A_{5})) \land\\{}(\forall p: \mathbb{N}, \operatorname{Prime}(p) \Rightarrow \forall P: \operatorname{Type}, [\operatorname{Group}(P)], [\operatorname{Finite}(P)], \operatorname{IsPGroup}(p, P) \Rightarrow \forall q \in \operatorname{Hom}(G, P), (\neg\operatorname{Injective}(q) \land \operatorname{IsTrivialHom}(q))) \land\\{}\operatorname{primePowerResidual}(G) = \operatorname{topSubgroup}(G) \land\\{}\operatorname{primePowerQuotientObserver}(G) = 1 \land\\{}(\exists V: \operatorname{Type}, [\operatorname{AddCommGroup}(V)], [\operatorname{Module}(\operatorname{ZMod}(5), V)], \exists \rho \in \operatorname{Hom}(G, \operatorname{GL}(\operatorname{ZMod}(5), V)), (\operatorname{Injective}(\rho) \land \operatorname{kernel}(\rho) = \operatorname{trivialSubgroup}(G))) \land\\{}(\exists o_{q}, o_{\rho} \in \operatorname{LocalObserverAtPrime}(5, G), \operatorname{Kind}(o_{q}) = PrimePowerQuotient \land \operatorname{Kind}(o_{\rho}) = ResidueLinear \land \operatorname{Kind}(o_{q}) \neq \operatorname{Kind}(o_{\rho}) \land \neg\operatorname{Faithful}(o_{q}) \land \operatorname{Faithful}(o_{\rho})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ObserverTypes/AlternatingFiveObserverBlindKernelIrreplaceability.alternating_five_observer_blind_kernel_irreplaceability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a finite group G isomorphic to A5 such that every map from G to every finite p-group is both noninjective and the trivial map. Consequently the canonical prime-power residual is the whole group and the canonical joint quotient observer is constant.

For the same group there is an injective characteristic-five linear observer whose kernel is the trivial subgroup. At prime 5 this observer and a prime-power quotient observer have distinct kinds and opposite fidelity.

## References

- Truth anchor: `D5/S3/Factorization/ObserverTypes/AlternatingFiveObserverBlindKernelIrreplaceability.alternating_five_observer_blind_kernel_irreplaceability`
- Dependency: [D5/S3/Factorization/ObserverTypes/AlternatingFiveObserverTypeIrreplaceability](AlternatingFiveObserverTypeIrreplaceability.md)
- Dependency: [D5/S3/Factorization/PrimePowers/AlternatingFiveResidualSeparation](../PrimePowers/AlternatingFiveResidualSeparation.md)
