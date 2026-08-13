# Additive Transport of a Multiplicative Cocycle

## Abstract

Homomorphic images turn multiplicative cocycle identities into additive ones.

**Theorem 1.1 (The transported cocycle law is additive).**

$$\forall G, A,\ [\operatorname{Monoid}(G)],\ [\operatorname{AddMonoid}(A)],\ \forall f: G \to^{*} \operatorname{Multiplicative}(A),\ \forall k_{\alpha\gamma}, k_{\alpha\beta}, k_{\beta\gamma}\in G,\ k_{\alpha\gamma}=k_{\alpha\beta} * k_{\beta\gamma} \Rightarrow \operatorname{toAdd}(f(k_{\alpha\gamma}))=\operatorname{toAdd}(f(k_{\alpha\beta}))+\operatorname{toAdd}(f(k_{\beta\gamma}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/AdditiveCocycleTransport.map_cocycle_to_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any monoid-valued cocycle, a homomorphism into the multiplicative type tag of an additive monoid sends the direct transition to the sum of the two successive transitions.

This declaration closes only the additive-transport continuation of the existing throat-transition cocycle. It assumes the multiplicative cocycle identity and proves its additive image; it makes no new existence or uniqueness claim for local lifts.

The pinned library supplies the complete proof mechanism: map_mul preserves the product, and Multiplicative.toAdd_mul identifies multiplication in the tagged codomain with addition. The Lean declaration is a thin wrapper around those laws.

## References

- Truth anchor: `D5/S1/Solenoid/AdditiveCocycleTransport.map_cocycle_to_additive`
